open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string                      
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool with show
                                                   
(* The type for the stack machine program *)
type prg = insn list
                            
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
        
(*let rec eval env ((cs, st, ((s, i, o) as c)) as config) prg =
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
        | LD x ->
            eval env (cs, (State.eval s x) :: st, (s, i, o)) rest
        | ST x ->
            let z :: st = st in
            eval env (cs, st, (State.update x z s, i, o)) rest
(* 	| STA (s, i) -> TODO*)
	    (* TODO *)
        | LABEL l -> eval env config rest
        | JMP l -> eval env config (env#labeled l)
        | CJMP (t, l) ->
            let z :: st = st in
            let config = (cs, st, c) in
            if ((t = "z") = ((Value.to_int z) = 0))
            then eval env config (env#labeled l)
            else eval env config rest
        | BEGIN (func, params, locals) ->
            let h, t = split_at (List.length params) st in
            let s' = State.enter s (params @ locals) in
            let s' = State.update_many params h s' in
            eval env (cs, t, (s', i, o)) rest
        | CALL (name, numparam, isfunc) ->
           eval env ((rest, s)::cs, st, (s, i, o)) (env#labeled name)
        | RET v ->
           let (p', s') :: cs = cs in
           eval env (cs, st, (State.leave s s', i, o)) p'
        | END ->
            match cs with
            | [] -> config
            | _  ->
               let (p', s') :: cs = cs in
               eval env (cs, st, (State.leave s s', i, o)) p'*)
let rec eval env ((cs, st, ((s, i, o) as c)) as config) prg = failwith "Unimplemented"

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
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
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
(*let compile dt =
  let ds, t = dt in
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.String s         -> [STRING s]
  | Expr.Array            -> [] (* TODO *)
  (* MORE TODO *)
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
  | Expr.Call (name, args) -> List.flatten (List.map expr (List.rev args)) @ [CALL (name, List.length args, false)]
  in
  let label_gen = make_label_gen () in
  let rec condcompile t =
    let label = label_gen () in
    let need, p = compile' label t in
    p @ (if need then [LABEL label] else [])
  and compile' outlabel t = match t with
    | Stmt.Seq (s1, s2)  ->
      let need, p = compile' outlabel s2 in
      need, condcompile s1 @ p
    | Stmt.Read x        -> false, [READ; ST x]
    | Stmt.Write e       -> false, expr e @ [WRITE]
    | Stmt.Assign (x, e) -> false, expr e @ [ST x]
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
    | Stmt.Call (name, args) -> false, List.flatten (List.map expr (List.rev args)) @ [CALL (name, List.length args, true)]
    | Stmt.Return me -> (match me with
                         | None -> false, [RET false]
                         | Some e -> false, expr e @ [RET true])
  in
  let compile_def d =
    let name, (params, locals, body) = d in
    [LABEL name; BEGIN (name, params, locals)] @ condcompile body @ [END]
  in
  condcompile t @ [END] @
  List.flatten (List.map compile_def ds)*)
let compile dt = failwith "Unimplemented"
