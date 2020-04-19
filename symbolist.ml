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
  | And
  | Or
  | Xor

type uop = 
  | Neg
  | Not
  | Sqrt
  | Log
  | Exp
  | Sin
  | Cos
  | Tan

type exp =
  | Int of int64 
  | Float of float 
  | Bool of bool 
  | Var of id
  | List of exp list
  | Bop of bop * exp * exp 
  | Uop of uop * exp 

(* A context to store the variables. *)
module Ctxt = struct
  type t = (id * exp) list
  let lookup ctxt ident = List.assoc ident ctxt 
end

(* grad: the symbolic differentiator. *)
let grad (ctxt : Ctxt.t) (dx : id) : exp = function
  | Int i -> Int 0 (* d/dx [c] = 0 *)
  | Var vid -> if vid == dx then Int 1 else Int 0 (* d/dx [x] = 1, d/dx [y] = 0 *) 
  | Bop (op, f, g) -> 
    begin match op with 
      | Add -> Bop (Add,  grad ctxt dx f, grad ctxt dx g) (* d/dx[f + g] = d/dx[f] + d/dx[g] *)
      | Sub -> Bop (Sub,  grad ctxt dx f, grad ctxt dx g) (* d/dx[f - g] = d/dx[f] = d/dx[g] *)
      | Mul -> Bop (Add,  Bop (Mul, grad ctxt dx f, g), Bop (Mul, f, grad ctxt dx g)) (* d/dx (f * g) = (d/dx f) * g + f * (d/dx g) *)
      | Div -> Bop (Div, Bop (Sub, Bop (Mul, g, grad ctxt dx f), Bop (Mul, f, grad ctxt dx g)),
          Bop (Mul, g, g)) (* d/dx[f/g] = (g*d/dx[f] - f*d/dx[g]) / (g*g) *)
      | _ -> failwith "grad: Invalid binary operator"
    end
  | Uop (op, f) -> 
    begin match op with 
      | Sqrt -> Bop (Mul, Int ())
    end
  | _ -> failwith "grad: Invalid type of expressions"
