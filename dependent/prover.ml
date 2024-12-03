let () = Printexc.record_backtrace true

(** Variables. *)
type var = string

(** Expressions. *)
type expr =
  | Type
  | Var of var
  | App of expr * expr
  | Abs of var * expr * expr
  | Pi of var * expr * expr
  | Nat
  | Z
  | S of expr
  | Ind of expr * expr * expr * expr 
  | Eq of expr * expr
  | Refl of expr
  | J of expr * expr * expr * expr * expr

(* Fill me in! *)
let rec to_string e =
  match e with
  | Type -> "Type"
  | Var x -> x
  | App (e1, e2) -> "(" ^ to_string e1 ^ " " ^ to_string e2 ^ ")"
  | Abs (x, e1, e2) -> "(fun : " ^ x ^ " : " ^ to_string e1 ^ " -> " ^ to_string e2 ^ ")"
  | Pi (x, e1, e2) -> "(Π " ^ x ^ " : " ^ to_string e1 ^ " -> " ^ to_string e2 ^ ")"
  | Nat -> "Nat"
  | Z -> "Z"
  | S e -> "( S " ^ to_string e ^ " )" 
  | _ -> failwith "not implemented"

  (*5.3 Fresh variable names*)

let i = ref 0
let fresh_var = 
  i := !i + 1;
  "x" ^ string_of_int !i

(* let () = let x = fresh_var in print_endline x *)

(*5.4 Substitution*)
(*substitution of x by t in u*)
let rec subst x t u = 
  match u with
  | Var y -> if x = y then t else u
  | Type -> u (*check ?*)
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (y, u1, u2) -> let f = fresh_var in
  if x = y then (*x appears in the terms but is not free so we can just rename it*)
    Abs (f, subst x t u1, subst y (Var f) u2) (*car alors x ne peut pas être libre dans u2*)
  else Abs (f , (subst x t u1), (subst x t (subst y (Var f) u1)))(*problem if y is not free in t*)
  | Pi (y, u1, u2) -> let f = fresh_var in 
  if x = y then Pi (f, subst x (Var f) u1, subst x (Var f) u2) (*not necessary, is it ?*)
  else Pi (f, subst x t (subst x (Var f) u1), subst x t (subst x (Var f) u2)) (*check again for the pb of FV...*)
  | _ -> failwith ("not implemented yet")

  (* 5.5 Contexts *)

type context = (var * (expr * expr option)) list

(* 5.6 Normalization *)
let rec normalize e ctx = 
  match e with
  | Type -> e
  | Var x -> (match (List.assoc x ctx) with | _, Some v -> v | _, None -> e)
  | App (u1, u2) -> (match u1 with
    | Abs (x, a, b) -> subst x (normalize u2 ctx) (normalize b ctx)
    | _ -> App (normalize u1 ctx, normalize u2 ctx)
    )
  | Pi (x, a, b) -> Pi (x, normalize a ctx, normalize b ctx)
  | Nat -> Nat
  | Z -> Z
  | S (ex) -> S (normalize ex ctx)
  | _ -> failwith "not implemented yet"

let rec string_of_context c = (*I need to add skipping line*)
  match c with 
  | [] -> ""
  | (x, (a,t))::q when t=None -> x^" : "^(to_string a)^"\n"^(string_of_context q)
  | (x, (a,Some v))::q -> x^" : "^to_string a^" = "^(to_string v)^(string_of_context q)
  |_ -> failwith ("? is that a context ?")

(*test*)
let () = print_endline(string_of_context [("x", (Type, None))])
let ()= print_endline(string_of_context [("x", (Type, Some Z))])

(* 5.7 α-conversion *)

let rec alpha t1 t2 = match t1,t2 with 
| Type,Type -> true
| Var x, Var y when x=y -> true
| App (e1, e2), App (f1, f2) -> ((alpha e1 f1) && (alpha e2 f2))
| Abs (v, e1, e2), Abs (w, f1, f2) -> (alpha e1 f1)&&(alpha e2 (subst w (Var v) f2))
| Pi (v, e1, e2), Pi (w, f1, f2) -> (alpha e1 f1)&&(alpha e2 (subst w (Var v) f2)) (*NOT SURE*)
| Nat, Nat -> true
| Z, Z -> true
| S n, S m -> alpha n m
| Ind (e1,e2,e3,e4), Ind (f1,f2,f3,f4) -> failwith "not implemented yet"
| Eq (e1, e2), Eq (f1,f2) -> failwith "not implemented yet"
| Refl e, Refl f -> failwith "not implemented yet"
| J (e1,e2,e3,e4,e5), J (f1,f2,f3,f4,f5) -> failwith "not implemented yet"
| _ -> false


(* 5.8 Conversion *)

let conv ctx t1 t2 =
  alpha (normalize t1 ctx) (normalize t2 ctx)

  (* 5.9 Type inference and 5.10 Type checking*)

exception Type_error of string

(* infers the type of e in the context ctx *)
(*But we need to check that the context is*)
let rec infer ctx e = match e with
| Type -> Type (*REALLY ?*)
| Var v -> (try (fst (List.assoc v ctx)) with | Not_found -> raise (Type_error "v is not defined"))
| App (e1, e2) -> (match (infer ctx e1) with | Pi(v,x,y) -> check ctx e2 x; infer ctx (subst x e2 y) | _ -> raise Type_error("not a function type") ) (*should we change the context ?*)
| Abs (v,e,f) -> check ctx e Type; Pi (v,e,infer ((v, (e,None))::ctx) f)
| Pi (v, x, y) -> Type
| Nat -> Type
| Z -> Nat
| S(e) -> (try (check ctx e Nat) with |_ -> raise (Type_error("Successor should take an int"))); Nat
| Ind (e1,e2,e3,e4) -> failwith "not implemented yet"
| Eq (e1,e2) -> failwith "not implemented yet"
| Refl(s) -> failwith "not implemented yet"
| J (e1,e2,e3,e4,e5) -> failwith "not implemented yet"
| _ -> failwith "what are you talking about ?"

and check ctx e t = 
if (infer ctx e) <> t then raise(Type_error("Type mismatch")) else ()