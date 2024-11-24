let () = Printexc.record_backtrace true


open Expr

(** Variables. *)
type var = string


let ty_of_string s = Parser.ty Lexer.token (Lexing.from_string s)

let tm_of_string s = Parser.tm Lexer.token (Lexing.from_string s)


(* 1.3 String representation *)

let rec string_of_ty some_type =
  match some_type with 
  | TVar s -> s
  | Arr(ty1,ty2) -> "( "^(string_of_ty ty1)^" => "^(string_of_ty ty2)^" )"
  | Conj(ty1,ty2) -> "( "^(string_of_ty ty1)^" /\\ "^(string_of_ty ty2)^" )"
  | TTruth -> "T"
  | Coprod(ty1,ty2) -> "( "^(string_of_ty ty1)^" + "^(string_of_ty ty2)^" )"
  | Zero -> "0"

let rec string_of_tm some_term = 
  match some_term with 
  |Var s -> s
  |App(tm1,tm2) -> "( "^(string_of_tm tm1)^" "^(string_of_tm tm2)^" )"
  |Abs(var1, ty1, tm1) -> "(fun : "^var1^" : "^(string_of_ty ty1)^" -> "^(string_of_tm tm1)
  |Pair(tm1,tm2) -> "( "^(string_of_tm tm1)^" and "^(string_of_tm tm2)^" )"
  |Fst(tm1) -> "(fst ("^(string_of_tm tm1)^") )"
  |Snd(tm1) -> "(snd ("^(string_of_tm tm1)^") )" 
  |True -> "True"
  |InjLeft(ty1,tm1) -> "(injleft_"^(string_of_ty ty1)^" ( "^(string_of_tm tm1)^" ) )"
  |InjRight(ty1,tm1) -> "(injright_"^(string_of_ty ty1)^" ( "^(string_of_tm tm1)^" ) )"
  |Case(tm0,tml,tmr) -> "(case ("^(string_of_tm tm0)^") : "^(string_of_tm tml)^" , "^(string_of_tm tmr)^" ) "
  (* |Case_type(ty1,tm1) -> "(case_"^(string_of_ty ty1)^" ( "^(string_of_tm tm1)^" ) )"  *)
  |Case_type(tm1)-> "(case ("^(string_of_tm tm1)^") )"
  (*add Injleft, case etc*)
(*tests?*)

(* 1.4 Type inference *) (* --> to 1.6 Type inference and checking together *)

type context = (var * ty) list

exception Type_error

let rec infer_type env t =
  match t with
  | Var x -> (try List.assoc x env with Not_found -> raise Type_error)
  | Abs (x, a, t1) -> Arr (a, infer_type ((x,a)::env) t1)
  | App (t1, u) ->
     (match infer_type env t1 with
     | Arr (a, b) -> check_type env u a; b
     | _ -> raise Type_error) 
  | Pair(t1,u) -> Conj(infer_type env t1, infer_type env u)
  | Fst t1 -> (match infer_type env t1 with 
    | Conj(a,_) -> a
    | _ -> raise Type_error) 
  | Snd t1 -> (match infer_type env t1 with
    | Conj (_, b) -> b
    | _ -> raise Type_error)  
  | True -> TTruth
  (* | Case(t1,(var_u,u),(var_v,v)) -> (match infer_type env t1 with
    |Coprod(a,b)-> (let c_u = infer_type ((var_u,a)::env) u in
     check_type ((var_v,b)::env) v c_u; c_u
     )
    | _ -> raise Type_error)
   *)
  | Case(t1,tml,tmr) -> (
    match infer_type env t1 with
    |Coprod(a,b)-> (let t_u = infer_type env tml in
     match t_u with |Arr(x,c) when x=a -> check_type env tmr (Arr(b,c)); c (*only problem with x=a*)
     | _ -> raise Type_error
     )
    | _ -> raise Type_error )
  | InjLeft(typ,t1) -> let a = infer_type env t1 in Coprod(a,typ)
  | InjRight(typ,t1) -> let b = infer_type env t1 in Coprod(typ,b)
  | Case_type(_) -> raise Type_error (*?should not happen??*)
 (*I DON'T UNDERSTAND*)
and check_type env tm a = 
  match tm with |Case_type (t2)-> check_type env t2 Zero
  |_-> (
  let t = infer_type env tm in
  if (a <> Zero)  && (t <> a) then raise Type_error )
    (*&& (t <> Zero) ???*)
(*it is also ok if infer_type env tm = case(Zero)*)
  
    (*type checking tests*)

(* let () = let just_a = Abs("x", TVar "A", Var "x") 
 in print_endline (string_of_ty (infer_type [] just_a)); *)

(* check_type [] just_a (Arr(TVar "B", TVar "B")); *)
(* check_type [] just_a (TVar "a") *)

    (* 1.7 Other connectives *)
    (* 1.8 Conjunction *)

    (* In order to test it, write a term and_comm witnessing the commutativity of conjunction:
print_endline (string_of_ty (infer_type [] and_comm)) *)


  (* in print_endline (string_of_tm and_comm)  *)

let () = 
let and_comm : tm =  
  Abs("t", Conj(TVar "A", TVar "B"),  Pair(Snd (Var "t"), Fst (Var "t") ) ) 
in print_endline (string_of_ty (infer_type [] and_comm))

(* it works !*)

(* 1.9 Truth *)

let () =  
let true_term : tm = 
  Abs("t", Arr(TTruth, TVar "A"), App(Var "t", True) ) 
in print_endline (string_of_ty (infer_type [] true_term))

(* it works !*)

(* 1.10 Disjunction *)
let () =  
let coprod_commute = Abs("t", Coprod(TVar "A",TVar "B"), Case (Var "t", Abs("t",TVar "A", InjRight(TVar"B", Var "t")), Abs("t", TVar "B", InjLeft(TVar"A", Var "t"))) ) in
print_endline (string_of_ty (infer_type [] coprod_commute))

(* 1.11 Falsity *)

(*I first prove ( 0 => B )*)

let ()=
let false_implies_anything = Abs("t", Zero, App(Abs("x",TVar "B", Var "x"), Case_type(Var "t"))) in
print_endline (string_of_ty (infer_type [] false_implies_anything))


let () = 
let falsity_term = Abs("p",Conj(TVar "A",Arr(TVar "A", Zero)),App(Snd(Var "p"),Fst(Var "p"))) in
print_endline (string_of_ty (infer_type [] falsity_term))

(* 1.12 Parsing strings *)

(* 2.1 String representation of contexts *)
let string_of_ctx c = 
  let string_of_couple (x,t) = string_of_tm x^" : "^string_of_ty t in
  String.concat "," (List.map string_of_couple c)

  (* 2.2 Sequents *)

  type sequent = context * ty

  let string_of_sequent (c,t) = string_of_ctx c^" |- "^string_of_ty t
