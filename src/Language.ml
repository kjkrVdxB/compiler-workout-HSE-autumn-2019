(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators

(* Values *)
module Value =
  struct

    @type t = Int of int | String of bytes | Array of t array | Sexp of string * t list (*with show*)

    let to_int = function 
    | Int n -> n 
    | _ -> failwith "int value expected"

    let to_string = function 
    | String s -> Bytes.to_string s 
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, vs)
    let of_int    n = Int    n
    let of_string s = String (Bytes.of_string s)
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s 
    let update_array  a i x = a.(i) <- x; a
                      
  end
       
(* States *)
module State =
  struct
                                                                
    (* State: global state, local state, scope variables *)
    type t =
    | G of (string -> Value.t)
    | L of string list * (string -> Value.t) * t

    (* Undefined state *)
    let undefined x = failwith (Printf.sprintf "Undefined variable: %s" x)

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y 

    (* Empty state *)
    let empty = G undefined

    (* Update: non-destructively "modifies" the state s by binding the variable x 
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | G s -> G (bind x v s)
      | L (scope, s, enclosing) ->
         if List.mem x scope then L (scope, bind x v s, enclosing) else L (scope, s, inner enclosing)
      in
      inner s
      
    let rec update_many xs vs s = match xs with
      | [] -> s
      | x::xs -> update_many xs (List.tl vs) (update x (List.hd vs) s)

    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | G s -> s x
      | L (scope, s, enclosing) -> if List.mem x scope then s x else eval enclosing x

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | G _ as st -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Push a new local scope *)
    let push st s xs = L (xs, s, st)

    (* Drop a local scope *)
    let drop (L (_, _, e)) = e
                               
  end

(* Builtins *)
module Builtin =
  struct
      
    let eval (st, i, o, _) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, Some (Value.of_int z)) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], None)
    | ".elem"    -> let [b; j] = args in
                    (st, i, o, let i = Value.to_int j in
                               Some (match b with
                                     | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                     | Value.Array    a  -> a.(i)
                                     | Value.Sexp (_, a) -> List.nth a i
                               )
                    )         
    | ".length"     -> (st, i, o, Some (Value.of_int (match List.hd args with Value.Sexp (_, a) -> List.length a | Value.Array a -> Array.length a | Value.String s -> Bytes.length s)))
    | ".array"      -> (st, i, o, Some (Value.of_array @@ Array.of_list args))
    | "isArray"  -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.Array  _ -> 1 | _ -> 0))
    | "isString" -> let [a] = args in (st, i, o, Some (Value.of_int @@ match a with Value.String _ -> 1 | _ -> 0))                     
       
  end
    
(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    
    (* The type for expressions. Note, in regular OCaml there is no "@type..." 
       notation, it came from GT. 
    *)
    @type t =
    (* integer constant   *) | Const  of int
    (* array              *) | Array  of t list
    (* string             *) | String of string
    (* S-expressions      *) | Sexp   of string * t list
    (* variable           *) | Var    of string
    (* binary operator    *) | Binop  of string * t * t
    (* element extraction *) | Elem   of t * t
    (* length             *) | Length of t 
    (* function call      *) | Call   of string * t list with show

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* The type of configuration: a state, an input stream, an output stream, an optional value *)
    type config = State.t * int list * int list * Value.t option
                                                            
    (* Expression evaluator

          val eval : env -> config -> t -> int * config


       Takes an environment, a configuration and an expresion, and returns another configuration. The 
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration, 
       an returns a pair: the return value for the call and the resulting configuration
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
    
    let rec eval env ((s, i, o, _) as config) expr =
    match expr with
      | Const n ->
         (s, i, o, Some (Value.of_int n))
      | Var   x ->
         (s, i, o, Some (State.eval s x))
      | Binop (op, x, y) ->
         let config = eval env config x in
         let _, _, _, Some r1 = config in
         let config = eval env config y in
         let s, i, o, Some r2 = config in
         (s, i, o, Some (Value.of_int ((to_func op) (Value.to_int r1) (Value.to_int r2))))
      | Call (f, args) ->
         let argvals, config = eval_list env config args in
         env#definition env f argvals config
      | Array a ->
	let argvals, config = eval_list env config a in
	(s, i, o, Some (Value.of_array (Array.of_list argvals)))
      | String str ->
	(s, i, o, Some (Value.of_string str))
      | Sexp (c, es) ->
	let vals, (s, i, o, _) = eval_list env config es in
	(s, i, o, Some (Value.sexp c vals))
      | Elem (a, sub) ->
	let config = eval env config a in
	let _, _, _, Some a = config in
	let config = eval env config sub in
	let _, _, _, Some sub = config in
	Builtin.eval config [a; sub] ".elem"
      | Length a ->
	let config = eval env config a in
	let _, _, _, Some a = config in
	Builtin.eval config [a] ".length"
	
    and eval_list env config es =
      List.fold_left
        (fun (vs, config) e ->
          let config = eval env config e in
          let s, i, o, Some r = config in
          vs @ [r], (s, i, o, None)) ([], config) es
         
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
	     mbsubslen);
	     
      
      mbsubslen: 
        base:(a:primary ixs:(-"[" parse -"]")* { List.fold_left (fun a x -> Elem (a, x)) a ixs }) l:("." %"length")? { match l with None -> base | Some _ -> Length base };

      primary:
        n:DECIMAL {Const n}
      | fun_name:IDENT "(" args:!(Util.list0 parse) ")" { Call (fun_name, args) }
      | -"(" parse -")"
      | "[" elems:!(Util.list0 parse) "]" { Array elems }
      | s:STRING { String (String.sub s 1 ((String.length s) - 2)) }
      | c:CHAR { Const (Char.code c) }
      | x:IDENT { Var x }
      | "`" ctr:IDENT els:(-"(" !(Util.list parse) -")")? { Sexp (ctr, match els with None -> [] | Some l -> l) } 
    )
    
  end
                    
(* Simple statements: syntax and sematics *)
module Stmt =
  struct

    (* Patterns in statements *)
    module Pattern =
      struct

        (* The type for patterns *)
        @type t =
        (* wildcard "_"     *) | Wildcard
        (* S-expression     *) | Sexp   of string * t list
        (* identifier       *) | Ident  of string
        with show, foldl

        (* Pattern parser *)                                 
        ostap (
          parse: 
	    "`" ctr:IDENT els:(-"(" !(Util.list parse) -")")? { Sexp (ctr, match els with None -> [] | Some l -> l) } 
	  | "_" { Wildcard }
	  | x:IDENT { Ident x }
        )
        
        let vars p =
          transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Ident s _ name = name::s end) [] p         
      end
        
    (* The type for statements *)
    @type t =
    (* assignment                       *) | Assign of string * Expr.t list * Expr.t
    (* composition                      *) | Seq    of t * t 
    (* empty statement                  *) | Skip
    (* conditional                      *) | If     of Expr.t * t * t
    (* loop with a pre-condition        *) | While  of Expr.t * t
    (* loop with a post-condition       *) | Repeat of t * Expr.t
    (* pattern-matching                 *) | Case   of Expr.t * (Pattern.t * t) list
    (* return statement                 *) | Return of Expr.t option
    (* call a procedure                 *) | Call   of string * Expr.t list 
    (* leave a scope                    *) | Leave  with show
                                                                                   
    (* Statement evaluator

         val eval : env -> config -> t -> config

       Takes an environment, a configuration and a statement, and returns another configuration. The 
       environment is the same as for expressions
    *)
    let update st x v is =
      let rec update a v = function
      | []    -> v           
      | i::tl ->
          let i = Value.to_int i in
          (match a with
           | Value.String s when tl = [] -> Value.String (Value.update_string s i (Char.chr @@ Value.to_int v))
           | Value.Array a               -> Value.Array  (Value.update_array  a i (update a.(i) v tl))
           ) 
      in
      State.update x (match is with [] -> v | _ -> update (State.eval st x) v is) st
      
    let rec match_one_cont v p s = match p with
    | Pattern.Wildcard -> Some s
    | Pattern.Ident x -> Some (State.bind x v s)
    | Pattern.Sexp (pc, ps) -> match v with
      | Value.Sexp (c, vs) -> 
        if c <> pc then None
        else match_list vs ps s
      | _ -> None
    and match_list vs ps s = List.fold_left 
      (fun prev (v, p) -> match prev with 
          | None -> None 
          | Some s -> match_one_cont v p s) 
      (Some s) (List.combine vs ps)
      
    let match_one v p = match_one_cont v p State.undefined
      
    let rec matc v pts = match pts with
      | [] -> failwith "Match failed"
      | (p, b)::rest ->
        let res = match_one v p in
        match res with
        | None -> matc v rest
        | Some s -> (Pattern.vars p), s, b
      
    let rec eval env ((s, i, o, r) as config) k stmt = match stmt with
        | Assign (name, subs, ex) ->
	   let subs, config = Expr.eval_list env config subs in
	   let s, i, o, Some r = Expr.eval env config ex in
	   let s = update s name r subs in
           eval env (s, i, o, None) Skip k
        | Seq (a, b) ->
           let cont = if k = Skip then b else Seq (b, k) in
           eval env config cont a
        | Skip -> (match k with Skip -> config | _ -> eval env config Skip k)
        | If (c, t, f) ->
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if Value.to_int r <> 0 then eval env (s, i, o, None) k t else eval env (s, i, o, None) k f
        | While (c, b) ->
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if Value.to_int r <> 0 then eval env (s, i, o, None) (Seq (stmt, k)) b else eval env (s, i, o, None) Skip k
        | Repeat (b, c) ->
          let config = eval env config Skip b in
          let config = Expr.eval env config c in
          let s, i, o, Some r = config in
          if Value.to_int r = 0 then eval env (s, i, o, None) k stmt else eval env (s, i, o, None) Skip k
        | Case (e, pts) -> 
          let config = Expr.eval env config e in
          let s, i, o, Some v = config in
          let xs, ns, b = matc v pts in
          eval env (State.push s ns xs, i, o, None) (Seq (Leave, k)) b
        | Call (f, args) ->
           let argvals, config = Expr.eval_list env config args in
           let config = env#definition env f argvals config in
           eval env config Skip k
        | Return me -> (match me with
                      | None -> config
                      | Some e -> Expr.eval env config e)
        | Leave ->
            let s = State.drop s in
            eval env (s, i, o, r) Skip k
         
    (* Statement parser *)
    ostap (
      ifcont: c:!(Expr.parse) %"then" b:stmts rest:elif { If (c, b, rest) };
      elif:
        %"elif" ifcont
      | %"else" stmts %"fi"
      | %"fi" { Skip };
      subscript: "[" e:!(Expr.parse) "]" { e };
      case: p:!(Pattern.parse) "->" b:parse { (p, b) };
      one_stmt:
        %"if" ifcont
      | %"while" c:!(Expr.parse) %"do" b:stmts %"od" { While (c, b) }
      | %"skip" { Skip }
      | %"for" init:stmts "," c:!(Expr.parse) "," post:stmts %"do" b:stmts %"od" { Seq (init, While (c, Seq (b, post))) }
      | %"repeat" b:stmts %"until" c:!(Expr.parse) { Repeat (b, c) }
      | %"case" e:!(Expr.parse) %"of" cases:!(Util.listBy)[ostap ("|")][case] %"esac" { Case (e, cases) }
      | %"return" e:!(Expr.parse) { Return Some e }
      | %"return" { Return None }
      | fun_name:IDENT "(" args:!(Util.list0 Expr.parse) ")" { Call (fun_name, args) }      
      | x:IDENT sub:!(Util.list0By)[ostap ("")][subscript] ":=" e:!(Expr.parse) { Assign (x, sub, e) };
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
      arg  : IDENT;
      parse: %"fun" name:IDENT "(" args:!(Util.list0 arg) ")"
         locs:(%"local" !(Util.list arg))?
        "{" body:!(Stmt.parse) "}" {
        (name, (args, (match locs with None -> [] | Some l -> l), body))
      }
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
         method definition env f args ((st, i, o, r) as conf) =
           try
             let xs, locs, s      =  snd @@ M.find f m in
             let st'              = List.fold_left (fun st (x, a) -> State.update x a st) (State.enter st (xs @ locs)) (List.combine xs args) in
             let st'', i', o', r' = Stmt.eval env (st', i, o, r) Stmt.Skip s in
             (State.leave st'' st, i', o', r')
           with Not_found -> Builtin.eval conf args f
       end)
      (State.empty, i, [], None)
      Stmt.Skip
      body
  in
  o

(* Top-level parser *)
let parse = ostap (!(Definition.parse)* !(Stmt.parse))
