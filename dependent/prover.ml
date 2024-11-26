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
  (* | Nat -> "Nat"
  | Z -> "Z"
  | S e -> "( S " ^ to_string e ^ " )" *)
  | _ -> failwith "not implemented"

  (*5.3 Fresh variable names*)

let i = ref 0
let fresh_var = 
  i := !i + 1;
  "x" ^ string_of_int !i

(* let () = let x = fresh_var in print_endline x *)

let rec subst x t u = 
  match u with
  | Var y -> if x = y then t else u
  | Type -> u (*check ?*)
  | App (u1, u2) -> App (subst x t u1, subst x t u2)
  | Abs (y, u1, u2) -> if x = y then Abs (fresh_var, subst x t u1, subst x t u2)
  else Abs (y, subst x t u1, subst x t u2)
  | Pi (y, u1, u2) -> if x = y then Pi (fresh_var, subst x t u1, subst x t u2)
  else Pi (y, subst x t u1, subst x t u2)
  | _ -> failwith ("not implemented yet")


type context = (var * (expr * expr option)) list

let rec string_of_context c = (*I need to add skipping line*)
  match c with 
  | [] -> ""
  | (x, (a,t))::q when t=None -> x^" : "^(to_string a)^(string_of_context q)
  | (x, (a,Some v))::q -> x^" : "^to_string a^" = "^(to_string v)^(string_of_context q)
  |_ -> failwith ("? is that a context ?")