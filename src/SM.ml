open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string
(* a label                         *) | LABEL of string
(* unconditional jump              *) | JMP   of string                                                                                                                
(* conditional jump                *) | CJMP  of string * string with show
                                                   
(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                         
let rec eval env config prg = 
    match prg with
    | [] -> config
    | (f :: rest) -> 
        match f with
        | BINOP op -> 
            let y :: x :: st, c = config in
            eval env (((Expr.get_op op) x y) :: st, c) rest
        | CONST i ->
            let st, c = config in
            eval env (i :: st, c) rest
        | READ ->
            let (st, (s, z :: i, o)) = config in
            eval env (z :: st, (s, i, o)) rest
        | WRITE ->
            let (z :: st, (s, i, o)) = config in
            eval env (st, (s, i, o @ [z])) rest
        | LD x ->
            let (st, (s, i, o)) = config in
            eval env ((s x) :: st, (s, i, o)) rest
        | ST x ->
            let (z :: st, (s, i, o)) = config in
            eval env (st, (Expr.update x z s, i, o)) rest
        | LABEL l -> eval env config rest
        | JMP l -> eval env config (env#labeled l)
        | CJMP (t, l) ->
            let (z :: st, c) = config in
            let config = (st, c) in
            if ((t = "z") = (z = 0))
            then eval env config (env#labeled l)
            else eval env config rest

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
  let (_, (_, _, o)) = eval (object method labeled l = M.find l m end) ([], (Expr.empty, i, [])) p in o
  
let make_label_gen () =
  let cnt = Base.ref 0 in
  fun () ->
    incr cnt;
    "label" ^ (string_of_int !cnt)

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile t =
  let rec expr = function
  | Expr.Var   x          -> [LD x]
  | Expr.Const n          -> [CONST n]
  | Expr.Binop (op, x, y) -> expr x @ expr y @ [BINOP op]
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
  in
  condcompile t
