
(** Type variables. *)
type tvar = string

(** Term variables. *)
type var = string

(* 1.1 Simple types

A simple type is either a type variable or an implication between simple types. Define a type ty for simple types. *)
type ty =
|TVar of tvar |Arr of ty*ty 
|Conj of ty*ty
|TTruth
|Coprod of ty*ty
|Zero
|Nat

(* 1.2 λ-terms

Define a type tm for λ-terms à la Church (the variables in abstractions are typed).
 *)

type tm = 
| Var of var 
| App of tm*tm 
| Abs of var*ty*tm 
| Pair of tm*tm | Fst of tm | Snd of tm
| True
| InjLeft of ty*tm | InjRight of ty*tm | Case of tm*var*tm*var*tm (*Mais on veut les 2 derniers tm de type abs ?*)
| Case_type of tm*ty (*create a function from false to any type*)
| Nul | Succ of tm | Rec of tm*tm*var*tm (*Rec(a,b,v,c) = b if a=0 and c where we add a otherwise ? We will see...*)
  (*rec(t,)*)