open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP of string
(* put a constant on the stack     *) | CONST of int                 
(* read to stack                   *) | READ
(* write from stack                *) | WRITE
(* load a variable to the stack    *) | LD    of string
(* store a variable from the stack *) | ST    of string with show

(* The type for the stack machine program *)                                                               
type prg = insn list

(* The type for the stack machine configuration: a stack and a configuration from statement
   interpreter
 *)
type config = int list * Stmt.config

(* Stack machine interpreter

     val eval : config -> prg -> config

   Takes a configuration and a program, and returns a configuration as a result
 *)                         
let rec eval config prg = 
    match prg with
    | [] -> config
    | (f :: rest) -> 
        match f with
        | BINOP op -> 
            let y :: x :: st, c = config in
            eval (((Expr.get_op op) x y) :: st, c) rest
        | CONST i ->
            let st, c = config in eval (i :: st, c) rest
        | READ ->
            let (st, (s, z :: i, o)) = config in
            eval (z :: st, (s, i, o)) rest
        | WRITE ->
            let (z :: st, (s, i, o)) = config in
            eval (st, (s, i, o @ [z])) rest
        | LD x ->
            let (st, (s, i, o)) = config in
            eval ((s x) :: st, (s, i, o)) rest
        | ST x ->
            let (z :: st, (s, i, o)) = config in
            eval (st, (Expr.update x z s, i, o)) rest

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i = let (_, (_, _, o)) = eval ([], (Language.Expr.empty, i, [])) p in o

let rec compile_ex expr =
    match expr with
    | Expr.Const n -> [CONST n]
    | Expr.Var x -> [LD x]
    | Expr.Binop (op, e1, e2) -> (compile_ex e1) @ (compile_ex e2) @ [BINOP op]

(* Stack machine compiler

     val compile : Language.Stmt.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
 *)
let rec compile stmt =
    match stmt with
    | Stmt.Read x -> [READ; ST x]
    | Stmt.Write ex -> (compile_ex ex) @ [WRITE]
    | Stmt.Assign (x, ex) -> (compile_ex ex) @ [ST x]
    | Stmt.Seq (s1, s2) -> (compile s1) @ (compile s2)
