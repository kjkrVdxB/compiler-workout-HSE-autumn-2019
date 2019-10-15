(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators
                         
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
    let enter st xs = {empty with g = st.g; scope = xs}

    (* Drops a scope *)
    let leave st st' = {st' with g = st.g}

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
    (* binary operator  *) | Binop of string * t * t
    (* function call    *) | Call  of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * int option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns resulting configuration
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


    let rec eval_list env config es =
      List.fold_left
        (fun (vs, config) e ->
          let config = eval env config e in
          let s, i, o, Some r = config in
          vs @ [r], (s, i, o, None)) ([], config) es
    and eval env ((s, i, o, _) as config) expr =
      match expr with
      | Const n ->
         (s, i, o, Some n)
      | Var   x ->
         (s, i, o, Some State.eval s x)
      | Binop (op, x, y) ->
         let config = eval env config x in
         let _, _, _, Some r1 = config in
         let config = eval env config y in
         let s, i, o, Some r2 = config in
         (s, i, o, Some to_func op r1 r2)
      | Call (f, args) ->
         let argvals, config = eval_list env config args in
         env#definition env f argvals config
         
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
      | fun_name:IDENT "(" args:!(Util.list0By)[ostap (",")][parse] ")" { Call (fun_name, args) }
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
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list with show
                                                                    
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let rec eval env ((s, i, o, _) as config) k stmt = match stmt with
        | Read name ->
           let z :: i = i in
           eval env (State.update name z s, i, o, None) Skip k
        | Write ex ->
           let s, i, o, Some r = Expr.eval env config ex in
           eval env (s, i, o @ [r], None) Skip k
        | Assign (name, ex) ->
           let s, i, o, Some r = Expr.eval env config ex in
           eval env (State.update name r s, i, o, None) Skip k
        | Seq (a, b) ->
           let cont = if k = Skip then b else Seq (b, k) in
           eval env config cont a
        | Skip -> (match k with Skip -> config | _ -> eval env config Skip k)
        | If (c, t, f) ->
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if r <> 0 then eval env (s, i, o, None) k t else eval env (s, i, o, None) k f
        | While (c, b) ->
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if r <> 0 then eval env (s, i, o, None) (Seq (stmt, k)) b else eval env (s, i, o, None) Skip k
        | Repeat (b, c) ->
          let config = eval env config Skip b in
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if r = 0 then eval env (s, i, o, None) k stmt else eval env (s, i, o, None) Skip k
        | Call (f, args) ->
           let argvals, config = Expr.eval_list env config args in
           let config = env#definition env f argvals config in
           eval env config Skip k
        | Return me -> match me with
                      | None -> config
                      | Some e -> Expr.eval env config e
         
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
      | fun_name:IDENT "(" args:!(Util.list0By)[ostap (",")][Expr.parse] ")" { Call (fun_name, args) }
      | "return" e:!(Expr.parse) { Return Some e }
      | "return" { Return None };
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
  let m          = List.fold_left (fun m ((name, _) as def) -> M.add name def m) M.empty defs in  
  let _, _, o, _ =
    Stmt.eval
      (object
         method definition env f args (st, i, o, r) =
           let xs, locs, s      =  snd @@ M.find f m in
           let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
           let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
           (State.leave st'' st, i', o', r')
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
