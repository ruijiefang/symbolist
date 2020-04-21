(* Symbolist - a lightweight engine for symbolic mathematics based on S-expressions *)
(* Author: Ruijie Fang *)
(* Version v0.1a *)

open Printf

(* A variable name instance *)
type id = string

(* An expression type. *)
type bop =
  | Add 
  | Sub
  | Mul 
  | Div

(* Unary operators. *)
type uop = 
  | Sqrt
  | Log
  | Exp
  | Sin
  | Cos
  | Tan

(* Binary operators. *)
type exp =
  | Int of int64
  | Float of float 
  | Var of id
  | Bop of bop * exp * exp 
  | Uop of uop * exp 
  | VarDecl of id * exp 
  | Grad of id * exp 

(* A context to store the variables. *)
module Ctxt = struct
  type t = (id * exp) list
  let lookup ctxt ident = List.assoc ident ctxt
  let add ctxt id exp = (id, exp) :: ctxt 
  let empty = []
end

(* A helper to simplify fractions. *)
(* TODO: Needs more work. Idea: Grab gcd of all coefficients
 * from polynomial-representation of top, btm recursively and
 * implement simplification of coefficients in these polynomials.*)
let simplify_frac = 
  let rec gcd u v = if v = 0L then u else gcd v (Int64.rem u v) in 
  function 
  | Bop (Div, Int u, Int v) -> let b = gcd u v in 
    Bop (Div, Int (Int64.div u b), Int (Int64.div v b)) 
  | _ -> failwith "simplify_frac: Cannot simplify complicated fractions or non-fractions!"

(* A helper to make constants. *)
let ( ~% ) c = Int c

(* A helper to make fractions. *)
let ( // ) top btm = (Bop (Div, top, btm))

(* A helper to define addition expressions. *)
let ( ++ ) a b = (Bop (Add, a, b))

(* A helper to define subtraction expressions. *)
let ( -- ) a b = (Bop (Sub, a, b))

(* A helper to define multiplication expressions. *)
let ( ** ) a b = (Bop (Mul, a, b))

(* string of a binary operator. *)
let string_of_bop = function 
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"

(* string of unary functions. *)
let string_of_uop = function
  | Sqrt -> "√"
  | Log  -> "lg"
  | Exp  -> "exp"
  | Sin  -> "sin"
  | Cos  -> "cos"
  | Tan  -> "tan"
  | Grad -> "d/dx"

(* string of an expression *)
let rec string_of_exp : (exp -> string) = function 
  | Int i -> "Int " ^ (Int64.to_string i)
  | Float f -> "Float" ^ (string_of_float f)
  | Var id -> "Var " ^ id
  | Bop (op, f, g) -> "(" ^ (string_of_bop op) ^ ", " ^ (string_of_exp f) ^ ", " ^ (string_of_exp g) ^ ")"
  | Uop (op, f) -> "(" ^ (string_of_uop op) ^ ", " ^ (string_of_exp f) ^ ")"
  | VarDecl (id, expr) -> "(VarDecl " ^ id ^ ", " ^ (string_of_exp expr) ^ ")"

(* grad: the symbolic differentiator. *)
let rec grad (ctxt : Ctxt.t) (dx : id) : (exp -> exp) = function
  | Int i -> ~%0L (* d/dx [c] = 0 *)
  | Var vid -> if vid = dx then Int 1L else Int 0L (* d/dx [x] = 1, d/dx [y] = 0 *) 
  | Bop (op, f, g) -> 
    begin match op with 
      | Add -> (grad ctxt dx f) ++ (grad ctxt dx g) (* d/dx[f + g] = d/dx[f] + d/dx[g] *)
      | Sub -> (grad ctxt dx f) -- (grad ctxt dx g) (* d/dx[f - g] = d/dx[f] = d/dx[g] *)
      | Mul -> ((grad ctxt dx f) ** g) ++ (f ** (grad ctxt dx g)) (* d/dx (f * g) = (d/dx f) * g + f * (d/dx g) *)
      | Div -> ((g ** grad ctxt dx f) -- (f ** grad ctxt dx g)) // (g ** g) (* d/dx[f/g] = (g*d/dx[f] - f*d/dx[g]) / (g*g) *)
    end
  | Uop (op, f) -> 
    begin match op with 
      | Sqrt -> (~%1L // ~%2L) ** (grad ctxt dx f) // (Uop (Sqrt, f)) (* d/dx[sqrt(f)] = 1/2 * d/dx[f] / sqrt[f] *)
      | Log -> (grad ctxt dx f) // f (* d/dx[log(f)] = 1/f * d/dx[f] *)
      | Exp -> (Uop (Exp, f)) ** (grad ctxt dx f) (* d/dx[exp(f)] = exp(f) * d/dx[f] *)
      | Sin -> (Uop (Cos, f)) ** (grad ctxt dx f) (* d/dx[sin(f)] = cos(f) * d/dx[f] *)
      | Cos -> (~%0L -- (Uop (Sin, f))) ** (grad ctxt dx f) (* d/dx[cos(f)] = -sin(f) * d/dx[f] *) 
      | Tan -> (~%1L ++ ((Uop (Tan, f)) ** (Uop (Tan, f)))) ** grad ctxt dx f (* d/dx[tan(f)] = (1 + tan(f)*tan(f)) * d/dx[f] *)
    end
  | _ -> failwith "grad: Invalid type of expressions"

(* evaluates an expression. *)
let rec eval (ctxt : Ctxt.t) : (exp -> (Ctxt.t * float)) = function 
  | Int i -> ctxt, Int64.float_of_bits i
  | Float f -> ctxt, f
  | Var vid -> 
    begin try ctxt, eval ctxt (Ctxt.lookup ctxt vid)
    with Not_found -> failwith ("eval: Cannot evaluate an expression with unknown variable" ^ vid) end
  | Bop (op, f, g) ->
    ctxt, (begin match op with 
     |  Add -> Float.add | Sub -> Float.sub
     | Mul -> Float.mul | Div -> Float.div end) (eval ctxt f) (eval ctxt g) 
  | Uop (op, f) -> 
    ctxt, if op != Grad then 
      (begin match op with 
        | Sqrt -> sqrt | Log -> log | Exp -> exp
        | Sin -> sin   | Cos -> cos | Tan -> tan end) (eval ctxt f)
      else eval Grad  
  | VarDecl (id, rhs) ->
    let ctxt' = Ctxt.add ctxt (id, rhs) in ctxt', 0.0

(* Utilities for parsing and lexing *)

(* A token type. *)
type term =
  | IntNode of int64
  | FloatNode of float
  | VarNode of string
  | UnaryOp of uop
  | BinaryOp of bop
  | DeclOp
  | LParOp
  | RParOp

(* Prettyprint codestream objects. *)
let to_string = function
  | BinaryOp bop -> string_of_bop bop
  | UnaryOp uop -> string_of_uop uop
  | DeclOp -> "Var"
  | LParOp -> "("
  | RParOp -> ")"
  | _ -> "<ident>" 

(* Given a character string. Tokenizes it into object format. 
 * Caveats: 
 *  The pattern-matching order of OCaml also dictates the
 *  precedence when resolving syntax ambiguities: e.g. a variable
 *  named "sqrt" will be parsed as a square root function, instead
 *  of a variable ID. Hence, function names are not allowed as 
 *  variable names. *)
let of_string = function
  | "+" -> BinaryOp Add
  | "-" -> BinaryOp Sub
  | "*" -> BinaryOp Mul
  | "/" -> BinaryOp Div
  | "sqrt" -> UnaryOp Sqrt
  | "log" -> UnaryOp Log
  | "sin" -> UnaryOp Sin
  | "cos" -> UnaryOp Cos
  | "tan" -> UnaryOp Tan
  | "Var" -> DeclOp
  | "("   -> LParOp
  | ")"   -> RParOp 
  | s -> 
    begin try
        let x = Int64.of_string s in IntNode x
      with Failure _ -> 
        begin try 
            let y = Float.of_string s in FloatNode y
          with Failure _ -> VarNode s
        end
    end

(* Parsing. LL(1) Grammar for S-expressions: *)
(* S ::=  <expr>
   <expr> ::= <id> 
   <expr> ::= ( <op> <expr> <exprs> )
   <exprs> ::= <expr> <exprs> | epsilon 
   <id> = [a-zA-Z0-9]* 
   <op> = + | - | * | / | uop | <id> 
*)

(* The following functions define a recursive-descent
 * parser for the above grammar. "parse_expr", "parse_op",
 * "parse_exprs" functions correspond to the nonterminal
 * rules specified above. Since the grammar is LL(1) and
 * we permit 1-symbol 'lookaheads', there is no backtracking. *)

(* a handy type decl to help working on lexed codestreams. *)
type cstream = (term * string) list

(* another handy decl for an ast node. 
 * we convert from astnode representation into expr representation
 * later, for sake of cleaniness and convenience. *)
type astnode = Node of term * astnode list

(* <op> = + | - | * | / | uop | <id> *)
let parse_op (l : cstream) : term * cstream = 
  match l with 
  | (a, s) :: t ->
    begin match a with 
      | BinaryOp _ | UnaryOp _ | DeclOp -> a, t
      | _ -> failwith @@ "parse_op: operator expected but got " ^ s
    end
  | [] -> failwith "parse_op: operator expected but got none"

(* <expr> ::= <id> | LParOp <op> <expr> <exprs> RParOp *)
let rec parse_expr (l: cstream) : astnode * cstream = 
  match l with 
  | (a, s) :: t ->
    begin match a with 
      | IntNode v -> Node (a, []), t
      | FloatNode v -> Node (a, []), t
      | VarNode v -> Node (a, []), t
      | LParOp ->  
        let op_node, op_stream = parse_op t in 
        let expr_node, expr_stream = parse_expr op_stream in 
        let exprs_node, exprs_stream = parse_exprs expr_stream in 
        begin match exprs_stream with 
          | (a1, s1) :: t1 -> 
            if a1 = RParOp then (Node (op_node, expr_node :: exprs_node)), t1
            else failwith @@ "parse_expr: illegal token: ')' expected but got " ^ s1
          | [] -> failwith @@ "parse_expr: unclosed parenthesis: ')' expected but got " ^ s
        end
      | _ -> failwith @@ "parse_expr: <expr> encountered: "^s
    end
  | [] -> failwith "parse_expr: <expr> is not nullable but encountered null input"
and parse_exprs (l : cstream) : astnode list * cstream = 
  (* <exprs> ::= <expr> <exprs> | epsilon *)
  match l with 
  | (a, s) :: t ->
    let expr_node, expr_stream = parse_expr t in 
    let exprs_node, exprs_stream = parse_exprs expr_stream in 
    expr_node :: exprs_node, exprs_stream 
  | [] -> [], l (* epsilon *)


(* Lexing helpers. *)
let tokenize (s : string) : string list = Str.split (Str.regexp "[ \t]+") s

(* expr_of_ast constructs an expression out of a parsed expression in ast format. *)
let expr_of_ast (t : ast) : exp = 
  let expect i l2 = if i <> List.length l2 then failwith "expect: error: operand length mismatch"
  let op_term, list_of_operands = t in 
    match op_term with 
    | IntNode i -> expect 0 list_of_operands; Int i 
    | FloatNode f -> expect 0 list_of_operands; Float f
    | VarNode var_id -> expect 0 list_of_opearnds; Var var_id
    | UnaryOp uop -> expect 1 list_of_operands; Uop (uop, expr_of_ast @@ List.ith list_of_operands 0)
    | BinaryOp bop ->  expect 2 list_of_operands; 
      let op1 = List.ith list_of_operands 0 in 
      let op2 = List.ith list_of_operands 1 in 
      Bop (bop, expr_of_ast op1, expr_of_ast op2)
    | DeclOp -> expect 2 list_of_operands;
      let var_name_t = List.ith list_of_operands 0 in 
      let var_exp = List.ith list_of_operands 1 in 
      begin match var_name_t with 
        | (VarNode var_id, []) -> 
          VarDecl (var_id, expr_of_ast var_exp)
        | _ -> failwith @@ "expr_of_ast: error: expected variable id but got " ^ (to_string var_name_t)
      end
    | _ -> failwith @@ "expr_of_ast: error: unexpected token: " ^ (to_string op_term)


(* parse: lexes and parses an input and returns an expr option type. *)
let parse (input : string) : exp option = 
  let tokenized = tokenize input in 
  let lexed = List.map (fun x -> (of_string x), x) tokenized in 
  begin try 
      let ast_root, _ = parse_expr lexed in 
      Some (expr_of_ast ast_root)
    with Error e -> 
      Printf.printf "parse: Parsing expression failed with error %s" e;
      None
  end


(* main entry of the program. *)
let () = 
  let test1 = ~%2L ** (Var "x") ++ ~%3L in
  let ctxt1 = (Ctxt.add Ctxt.empty "x" ~%3L) in
  let ddx_test1 = grad ctxt1 "x" test1 in 
  Printf.printf "expr := %s\n" @@ string_of_exp test1;
  Printf.printf "d/dx := %s\n" @@ string_of_exp ddx_test1

