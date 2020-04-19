(* Symbolist - a lightweight engine for symbolic mathematics based on S-expressions *)
(* Author: Ruijie Fang *)
(* Version v0.1a *)

open Printf

(* A variable name instance *)
type id = string

(* A symbolist expression. *)
type bop =
  | Add 
  | Sub
  | Mul 
  | Div

type uop = 
  | Sqrt
  | Log
  | Exp
  | Sin
  | Cos
  | Tan

type exp =
  | Int of int64
  | Float of float 
  | Var of id
  | List of exp list
  | Bop of bop * exp * exp 
  | Uop of uop * exp 

(* A context to store the variables. *)
module Ctxt = struct
  type t = (id * exp) list
  let lookup ctxt ident = List.assoc ident ctxt
  let store ctxt id exp = (id, exp) :: ctxt 
end

(* A helper to simplify fractions. *)
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

(* grad: the symbolic differentiator. *)
let rec grad (ctxt : Ctxt.t) (dx : id) : (exp -> exp)  = function
  | Int i -> ~%0L (* d/dx [c] = 0 *)
  | Var vid -> if vid == dx then Int 1L else Int 0L (* d/dx [x] = 1, d/dx [y] = 0 *) 
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
let rec eval (ctxt : Ctxt.t) : (exp -> float) = function 
  | Int i -> Int64.float_of_bits i
  | Float f -> f
  | Var vid -> 
    begin try eval ctxt (Ctxt.lookup ctxt vid)
    with Not_found -> failwith ("eval: Cannot evaluate an expression with unknown variable" ^ vid) end
  | Bop (op, f, g) ->
    (begin match op with 
     | Add -> Float.add | Sub -> Float.sub
     | Mul -> Float.mul | Div -> Float.div end) (eval ctxt f) (eval ctxt g) 
  | Uop (op, f) -> 
    (begin match op with 
     | Sqrt -> sqrt | Log -> log | Exp -> exp
     | Sin -> sin   | Cos -> cos | Tan -> tan end) (eval ctxt f)
  | _ -> failwith "eval: unsupported type of expression."


(* Applies the evaluator to each expression element on lists. *)
let map_eval (ctxt : Ctxt.t) = function
  | List exps -> List (List.map (fun x -> Float (eval ctxt x)) exps)
  | _ -> failwith "map_eval: Cannot map to other than lists."


 
