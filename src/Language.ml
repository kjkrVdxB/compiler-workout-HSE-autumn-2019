(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Ostap.Combinators

(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t = {g : string -> int; l : string -> int; scope : string list}

    (* Empty state *)
    let empty =
      let e x = failwith (Printf.sprintf "Undefined variable: %s" x) in
      {g = e; l = e; scope = []}

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let u x v s = fun y -> if x = y then v else s y in
      if List.mem x s.scope then {s with l = u x v s.l} else {s with g = u x v s.g}

    (* Evals a variable in a state w.r.t. a scope *)
    let eval s x = (if List.mem x s.scope then s.l else s.g) x

    (* Creates a new scope, based on a given state *)
    let push_scope st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let drop_scope st st' = {st' with g = st.g}

    let rec update_many xs vs s = match xs with
      | [] -> s
      | x::xs -> update_many xs (List.tl vs) (update x (List.hd vs) s)

  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant *) | Const of int
    (* variable         *) | Var   of string
    (* binary operator  *) | Binop of string * t * t with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)
      
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)                                                       
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)    
    
    let rec eval st expr =      
      match expr with
      | Const n -> n
      | Var   x -> State.eval st x
      | Binop (op, x, y) -> to_func op (eval st x) (eval st y)

    (* Expression parser. You can use the following terminals:

         IDENT   --- a non-empty identifier a-zA-Z[a-zA-Z0-9_]* as a string
         DECIMAL --- a decimal constant [0-9]+ as a string
                                                                                                                  
    *)
    ostap (                                      
      parse:
	  !(Ostap.Util.expr 
             (fun x -> x)
	     (Array.map (fun (a, s) -> a, 
                           List.map  (fun s -> ostap(- $(s)), (fun x y -> Binop (s, x, y))) s
                        ) 
              [|                
		`Lefta, ["!!"];
		`Lefta, ["&&"];
		`Nona , ["=="; "!="; "<="; "<"; ">="; ">"];
		`Lefta, ["+" ; "-"];
		`Lefta, ["*" ; "/"; "%"];
              |] 
	     )
	     primary);
      
      primary:
        n:DECIMAL {Const n}
      | x:IDENT   {Var x}
      | -"(" parse -")"
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* The type of configuration: a state, an input stream, an output stream *)
    type config = State.t * int list * int list 

    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment supplies the following method

           method definition : string -> (string list, string list, t)

       which returns a list of formal parameters and a body for given definition
    *)
    let rec eval env config stmt = match stmt with
        | Read name ->
          let s, z :: i, o = config in (State.update name z s, i, o)
        | Write ex ->
          let s, i, o = config in (s, i, o @ [Expr.eval s ex])
        | Assign (name, ex) ->
          let s, i, o = config in (State.update name (Expr.eval s ex) s, i, o)
        | Seq (a, b) -> eval env (eval env config a) b
        | Skip -> config
        | If (c, t, f) ->
          let s, _, _ = config in
          if (Expr.eval s c) <> 0 then eval env config t else eval env config f
        | While (c, b) ->
          let s, _, _ = config in
          if (Expr.eval s c) <> 0 then eval env (eval env config b) stmt else config
        | Repeat (b, c) ->
          let config = eval env config b in
          let s, _, _ = config in
          if (Expr.eval s c) = 0 then eval env config stmt else config
        | Call (name, args) ->
          let params, locals, body = env#definition name in
          let s, i, o = config in
          let argvals  = List.map (Expr.eval s) args in
          let s' = State.push_scope s (params @ locals) in
          let s' = State.update_many params argvals s' in
          let s', i, o = (eval env (s', i, o) body) in
          (State.drop_scope s' s, i, o)

                                
    (* Statement parser *)
    ostap (                                      
      ifcont: c:!(Expr.parse) "then" b:stmts rest:elif { If (c, b, rest) };
      elif:
        -"elif" ifcont
      | -"else" stmts -"fi"
      | "fi" { Skip };
      one_stmt:
        x:IDENT ":=" e:!(Expr.parse)    { Assign (x, e) }
      | "read" "(" x:IDENT ")"         { Read x }
      | "write" "(" e:!(Expr.parse) ")" { Write e }
      | -"if" ifcont
      | "while" c:!(Expr.parse) "do" b:stmts "od" { While (c, b) }
      | "skip" { Skip }
      | "for" init:stmts "," c:!(Expr.parse) "," post:stmts "do" b:stmts "od" { Seq (init, While (c, Seq (b, post))) }
      | "repeat" b:stmts "until" c:!(Expr.parse) { Repeat (b, c) }
      | fun_name:IDENT "(" args:!(Util.list0By)[ostap (",")][Expr.parse] ")" { Call (fun_name, args) };
      stmts: <s::ss> : !(Util.listBy)[ostap (";")][one_stmt] { List.fold_left (fun a b -> Seq (a, b)) s ss };
      parse: stmts
    )
      
  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: name, argument list, local variables, body *)
    type t = string * (string list * string list * Stmt.t)

    ostap (
      locals: -"local" !(Util.listBy)[ostap (",")][ostap(IDENT)] | empty {[]};
      parse:  "fun" name:IDENT "(" params:!(Util.list0By)[ostap (",")][ostap(IDENT)] ")" l:locals "{" body:!(Stmt.parse) "}" { name, (params, l, body) }
    )

  end
    
(* The top-level definitions *)

(* The top-level syntax category is a pair of definition list and statement (program body) *)
type t = Definition.t list * Stmt.t    

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (defs, body) i =
  let module M = Map.Make (String) in
  let m        = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o  = Stmt.eval (object method definition f = snd @@ M.find f m end) (State.empty, i, []) body in o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
