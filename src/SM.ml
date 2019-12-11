open GT       
open Language
      
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                  
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.eprintf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
  interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

    val eval : env -> config -> prg -> config

  Takes an environment, a configuration and a program, and returns a configuration as a result. The
  environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env ((cs, st, ((s, i, o) as c)) as config) prg =
    match prg with
    | [] -> config
    | (f :: rest) ->
        match f with
        | BINOP op ->
            let y :: x :: st = st in
            eval env (cs, Value.of_int ((Expr.to_func op) (Value.to_int x) (Value.to_int y)) :: st, c) rest
        | CONST i ->
            eval env (cs, (Value.of_int i) :: st, c) rest
        | STRING s ->
            eval env (cs, (Value.of_string s) :: st, c) rest
        | SEXP (ctr, cnt) ->
            let elems, st = split cnt st in
            let elems = List.rev elems in
            eval env (cs, (Value.sexp ctr elems) :: st, c) rest
        | LD x ->
            eval env (cs, (State.eval s x) :: st, (s, i, o)) rest
        | ST x ->
            let z :: st = st in
            eval env (cs, st, (State.update x z s, i, o)) rest
        | STA (x, ic) ->
            let ixs, st = split ic st in
            let v::st = st in
            eval env (cs, st, (Stmt.update s x v ixs, i, o)) rest
        | LABEL l -> eval env config rest
        | JMP l -> eval env config (env#labeled l)
        | CJMP (t, l) ->
            let z :: st = st in
            let config = (cs, st, c) in
            if ((t = "z") = ((Value.to_int z) = 0))
            then eval env config (env#labeled l)
            else eval env config rest
        | BEGIN (func, params, locals) ->
            let h, t = split (List.length params) st in
            let h = List.rev h in
            let s' = State.enter s (params @ locals) in
            let s' = State.update_many params h s' in
            eval env (cs, t, (s', i, o)) rest
        | CALL (name, numparam, isproc) ->
            if env#is_label name then
              eval env ((rest, s)::cs, st, (s, i, o)) (env#labeled name)
            else
              eval env (env#builtin config name numparam isproc) rest
        | RET v ->
          let (p', s') :: cs = cs in
          eval env (cs, st, (State.leave s s', i, o)) p'
        | END ->
            (match cs with
            | [] -> config
            | _  ->
              let (p', s') :: cs = cs in
              eval env (cs, st, (State.leave s s', i, o)) p')
        | DROP ->
            let _::st = st in
            eval env (cs, st, c) rest
        | DUP ->
            let x::st = st in (* TODO: deep copy? *)
            eval env (cs, x :: x :: st, c) rest
        | SWAP ->
            let x::y::st = st in
            eval env (cs, y :: x :: st, c) rest
        | TAG ctr ->
            let x::st = st in
            let t = Value.tag_of x in
            eval env (cs, (Value.of_int (if t = ctr then 1 else 0)) :: st, c) rest
        | ENTER ls ->
            let s = State.push s State.undefined ls in
            let vs, st = split (List.length ls) st in
            let s = State.update_many ls (List.rev vs) s in
            eval env (cs, st, (s, i, o)) rest
        | LEAVE ->
            eval env (cs, st, (State.drop s, i, o)) rest

(* Top-level evaluation

    val run : prg -> int list -> int list

  Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (*print_prg p;*)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
        method is_label l = M.mem l m
        method labeled l = M.find l m
        method builtin (cstack, stack, (st, i, o)) f n p =
          let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
          let args, stack' = split n stack in
          let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
          let stack'' = if p then stack' else let Some r = r in r::stack' in
          (*Printf.printf "Builtin:\n";*)
          (cstack, stack'', (st, i, o))
      end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o
  
let make_label_gen () =
  let cnt = Base.ref 0 in
  fun () ->
    incr cnt;
    "label" ^ (string_of_int !cnt)
    
open Stmt
open Stmt.Pattern

(* Stack machine compiler

    val compile : Language.t -> prg

  Takes a program in the source language and returns an equivalent program for the
  stack machine
*)
let compile dt =
  let ds, t = dt in
  let rec expr = function
  | Expr.Var   x           -> [LD x]
  | Expr.Const n           -> [CONST n]
  | Expr.String s          -> [STRING s]
  | Expr.Array es          -> List.flatten (List.map expr es) @ [CALL (".array", List.length es, false)]
  | Expr.Sexp (c, es)      -> List.flatten (List.map expr es) @ [SEXP (c, List.length es)]
  | Expr.Elem (e, i)       -> expr e @ expr i @ [CALL (".elem", 2, false)]
  | Expr.Length e          -> expr e @ [CALL (".length", 1, false)]
  | Expr.Binop (op, x, y)  -> expr x @ expr y @ [BINOP op]
  | Expr.Call (name, args) -> List.flatten (List.map expr args) @ [CALL ("L" ^ name, List.length args, false)]
  in
  let label_gen = make_label_gen () in
  let rec check_pt pt faillabel ixs = match pt with
    | Wildcard -> []
    | Ident _  -> []
    | Sexp (c, pts) ->
      [DUP] @ List.flatten (List.map (fun x -> [CONST x; CALL (".elem", 2, false)]) ixs) @
      [DUP; TAG c; CJMP ("z", faillabel)] @
      [DUP; CALL (".length", 1, false); CONST (List.length pts); BINOP ("-"); CJMP ("nz", faillabel)] @
      [DROP] @ (* Drop local pattern *)
      List.flatten (List.map (fun pt, i -> 
        check_pt pt faillabel (ixs @ [i])
      ) (List.combine pts (List.init (List.length pts) (fun x -> x))))
  in
  let rec disassemble_pt pt ixs = match pt with
    | Wildcard -> []
    | Ident _  -> [DUP] @ List.flatten (List.map (fun x -> [CONST x; CALL (".elem", 2, false)]) ixs) @ [SWAP]
    | Sexp (c, pts) ->
      List.flatten (List.map (fun pt, i -> 
        disassemble_pt pt (ixs @ [i])
      ) (List.combine pts (List.init (List.length pts) (fun x -> x))))
  in
  let pattern pt faillabel =
    check_pt pt faillabel [] @
    disassemble_pt pt [] @
    [DROP] @ (* Drop root pattern *)
    [ENTER (List.rev (vars pt))]
  in
  let rec condcompile t =
    let label = label_gen () in
    let need, p = compile' label t in
    p @ (if need then [LABEL label] else [])
  and compile' outlabel t = match t with
    | Stmt.Seq (s1, s2)  ->
      let need, p = compile' outlabel s2 in
      need, condcompile s1 @ p
    | Stmt.Assign (x, ixs, e) -> (match ixs with
      | [] -> false, expr e @ [ST x]
      | _  -> false, List.flatten (List.map expr (e::(List.rev ixs))) @ [STA (x, List.length ixs)]
      )
    | Stmt.Skip          -> false, []
    | Stmt.If (c, t, f)  ->
      let els = label_gen () in
      let _, tp = compile' outlabel t in
      let _, fp = compile' outlabel f in
      true,
      expr c @
      [CJMP ("z", els)] @
        tp @ [JMP outlabel] @
      [LABEL els] @
        fp
    | Stmt.While (c, b)  ->
      let start = label_gen () in
      let test = label_gen () in
      let _, bp = compile' test b in
      false, [JMP test] @ [LABEL start] @ bp @ [LABEL test] @ expr c @ [CJMP ("nz", start)]
    | Stmt.Repeat (b, c) ->
      let start = label_gen () in
      false, [LABEL start] @ condcompile b @ expr c @ [CJMP ("z", start)]
    | Stmt.Case (e, pts) ->
      true,
      expr e @
      List.flatten (List.map (fun (pt, b) -> 
        let faillabel = label_gen () in
        let _, body = compile' outlabel b in
        pattern pt faillabel @ body @ [LEAVE] @ [JMP outlabel] @ 
        (match pt with Sexp _ -> [LABEL faillabel; DROP] | _ -> [])) 
        pts) (* Drop local pattern from before JMP faillabel *)
    | Stmt.Call (name, args) -> false, List.flatten (List.map expr args) @ [CALL ("L" ^ name, List.length args, true)]
    | Stmt.Return me -> (match me with
                        | None -> false, [RET false]
                        | Some e -> false, expr e @ [RET true])
  in
  let compile_def d =
    let name, (params, locals, body) = d in
    [LABEL ("L" ^ name); BEGIN (name, params, locals)] @ condcompile body @ [END]
  in
 (* print_prg (condcompile t @ [END] @
  List.flatten (List.map compile_def ds));*)
  condcompile t @ [END] @
  List.flatten (List.map compile_def ds)

