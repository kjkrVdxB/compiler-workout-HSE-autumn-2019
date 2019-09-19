(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT 
    
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
                                                            
    (* State: a partial map from variables to integer values. *)
    type state = string -> int 

    (* Empty state: maps every variable into nothing. *)
    let empty = fun x -> failwith (Printf.sprintf "Undefined variable %s" x)

    (* Update: non-destructively "modifies" the state s by binding the variable x 
      to value v and returns the new state.
    *)
    let update x v s = fun y -> if x = y then v else s y

        (* Make a bool operator return int; useful since every expression should evaluate to int *)
    let make_bool_result_int op x y =
        let v = op x y in
        if v then 1 else 0

    let make_bool_inputs_int op x y = op (x != 0) (y != 0)


    let get_op op =
        match op with
        | "+"  -> ( + )
        | "-"  -> ( - )
        | "*"  -> ( * )
        | "/"  -> ( / )
        | "%"  -> ( mod )
        | "<"  -> make_bool_result_int ( < )
        | "<=" -> make_bool_result_int ( <= )
        | ">"  -> make_bool_result_int ( > )
        | ">=" -> make_bool_result_int ( >= )
        | "==" -> make_bool_result_int ( == )
        | "!=" -> make_bool_result_int ( <> )
        | "&&" -> make_bool_result_int @@ make_bool_inputs_int ( && )
        | "!!" -> make_bool_result_int @@ make_bool_inputs_int ( || )
        | _ -> failwith (Printf.sprintf "Unknown operator %s" op)
        
    (* Expression evaluator

          val eval : state -> t -> int
 
       Takes a state and an expression, and returns the value of the expression in 
       the given state.
    *)

    let rec eval s e =
        match e with
        | Const c -> c
        | Var v -> s v
        | Binop (op, e1, e2) -> (get_op op) (eval s e1) (eval s e2)

  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* The type for statements *)
    @type t =
    (* read into the variable           *) | Read   of string
    (* write the value of an expression *) | Write  of Expr.t
    (* assignment                       *) | Assign of string * Expr.t
    (* composition                      *) | Seq    of t * t with show

    (* The type of configuration: a state, an input stream, an output stream *)
    type config = Expr.state * int list * int list 

    (* Statement evaluator

          val eval : config -> t -> config

       Takes a configuration and a statement, and returns another configuration
    *)
    let rec eval config e = 
        match e with
        | Read name -> 
            let s, z :: i, o = config in (Expr.update name z s, i, o)
        | Write ex ->
            let s, i, o = config in (s, i, o @ [Expr.eval s ex])
        | Assign (name, ex) ->
            let s, i, o = config in (Expr.update name (Expr.eval s ex) s, i, o)
        | Seq (a, b) -> eval (eval config a) b
                                                         
  end

(* The top-level definitions *)

(* The top-level syntax category is statement *)
type t = Stmt.t    

(* Top-level evaluator

     eval : int list -> t -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval i p =
  let _, _, o = Stmt.eval (Expr.empty, i, []) p in o
