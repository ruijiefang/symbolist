(* Symbolist - a lightweight engine for symbolic mathematics based on S-expressions *)
(* Author: Ruijie Fang *)
(* Version v0.1a *)

open Printf

(* A variable name instance *)
type id = string

(* A symbolist expressin. *)
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

type exp =
  | Int of int64  
  | Bool of bool 
  | Var of id
  | List of exp list
  | Bop of bop * exp list
  | Uop of uop * exp 

(* A context to store the variables. *)
module Ctxt = struct
  type t = (id * exp) list
  let lookup ctxt ident = List.assoc ident ctxt 
end

(* grad: the symbolic differentiator. *)
let grad (ctxt : Ctxt.t) (dx : id) : exp = function
  | Int i -> i
  | Var vid -> vid
  | Bop (op, l) -> 
    begin match op with 
      | Add -> Bop (Add,  List.map (grad ctxt) l)
      | Sub -> Bop (Sub,  List.map (grad ctxt) l)
      | Mul -> Bop (Add,  ) (* d/dx (f * g) = (d/dx f) * g + f * (d/dx g) *)
      | _ -> failwith "grad: Invalid binary operator"
    end
  | _ -> failwith "grad: Invalid type of expressions"
