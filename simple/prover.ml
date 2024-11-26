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
  | Conj(ty1,ty2) -> "( "^(string_of_ty ty1)^" ∧  "^(string_of_ty ty2)^" )"
  | TTruth -> "T"
  | Coprod(ty1,ty2) -> "( "^(string_of_ty ty1)^" ∨  "^(string_of_ty ty2)^" )"
  | Zero -> "_"
  | Nat -> "Nat"

let rec string_of_tm some_term = 
  match some_term with 
  |Var s -> s
  |App(tm1,tm2) -> "( "^(string_of_tm tm1)^" "^(string_of_tm tm2)^" )"
  |Abs(var1, ty1, tm1) -> "(fun : "^var1^" : "^(string_of_ty ty1)^" -> "^(string_of_tm tm1)^" )"
  |Pair(tm1,tm2) -> "( "^(string_of_tm tm1)^" , "^(string_of_tm tm2)^" )"
  |Fst(tm1) -> "(fst ("^(string_of_tm tm1)^") )"
  |Snd(tm1) -> "(snd ("^(string_of_tm tm1)^") )" 
  |True -> "True"
  |InjLeft(ty1,tm1) -> "(injleft_"^(string_of_ty ty1)^" ( "^(string_of_tm tm1)^" ) )"
  |InjRight(ty1,tm1) -> "(injright_"^(string_of_ty ty1)^" ( "^(string_of_tm tm1)^" ) )"
  |Case(tm0,varl,tml,varr,tmr) -> "(case ("^(string_of_tm tm0)^") : ( "^varl^" →  "^(string_of_tm tml)^" , "^varr^" → "^(string_of_tm tmr)^") "
  |Case_type(tm1,typ)-> "(case ("^(string_of_tm tm1)^") → "^(string_of_ty typ)^" )"
  |Nul -> "O"
  |Succ(tm1) -> "(succ ("^(string_of_tm tm1)^") )"
  |Rec(tm1,tm2,v,tm3) -> "(rec ("^(string_of_tm tm1)^" , "^(string_of_tm tm2)^" , "^v^" → "^(string_of_tm tm3)^"( "^string_of_tm tm1^") )"
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
  | Case(t1,varl,tml,varr,tmr) -> (
    match infer_type env t1 with
    |Coprod(a,b)-> (let c = infer_type ((varl,a)::env) tml in
     check_type ((varr,b)::env) tmr c; c 
     )
    | _ -> raise Type_error )
  | InjLeft(typ,t1) -> let a = infer_type env t1 in Coprod(a,typ)
  | InjRight(typ,t1) -> let b = infer_type env t1 in Coprod(typ,b)
  | Case_type(trm,typ) -> (if infer_type env trm == Zero then typ else raise Type_error) (*?should not happen??*)
  | Nul -> Nat
  | Succ(trm) -> (if infer_type env trm == Nat then Nat else raise Type_error)
  | Rec(trm1, trm2, v, trm3) -> (if (infer_type env trm1) == Nat then
    let a = infer_type env trm2 in
    check_type (("pred" , Nat)::(v , a)::env) trm3 a; a
  else raise Type_error)
and check_type env tm a = 
  let t = infer_type env tm in if (t <> a) then raise Type_error 
  
    (*type checking tests*)

(* let () = let just_a = Abs("x", TVar "A", Var "x") 
 in print_endline (string_of_ty (infer_type [] just_a)) *)

(* check_type [] just_a (Arr(TVar "B", TVar "B"));  *)
(* check_type [] just_a (TVar "A") *)

    (* 1.7 Other connectives *)
    (* 1.8 Conjunction *)

    (* In order to test it, write a term and_comm witnessing the commutativity of conjunction:
print_endline (string_of_ty (infer_type [] and_comm)) *)


  (* in print_endline (string_of_tm and_comm)  *)

(* let () = 
let and_comm : tm =  
  Abs("t", Conj(TVar "A", TVar "B"),  Pair(Snd (Var "t"), Fst (Var "t") ) ) 
in print_endline (string_of_ty (infer_type [] and_comm)) *)

(* it works !*)

(* 1.9 Truth *)

(* let () =  
let true_term : tm = 
  Abs("t", Arr(TTruth, TVar "A"), App(Var "t", True) ) 
in print_endline (string_of_ty (infer_type [] true_term)) *)

(* it works !*)

(* 1.10 Disjunction *)
(* let () =  
let coprod_commute = Abs("t", Coprod(TVar "A",TVar "B"), Case (Var "t", "t1", InjRight(TVar"B", Var "t1"), "t2",InjLeft(TVar"A", Var "t2")))  in 
print_endline (string_of_ty (infer_type [] coprod_commute)) *)

(* 1.11 Falsity *)

(* (A ∧ (A => ⊥) => B) *)


(*I first prove ( 0 => B )*)

(* let () =
let falsity_term = Abs("p",Conj(TVar "A",Arr(TVar "A", Zero)), Case_type(App(Snd(Var "p"),Fst(Var "p")),TVar "B")) in
print_endline (string_of_ty (infer_type [] falsity_term))  *)

(* 1.12 Parsing strings *)

(* 2.1 String representation of contexts *)
let string_of_ctx c = 
  let string_of_couple (x,t) =  x^" : "^string_of_ty t in
  String.concat "," (List.map string_of_couple c)

  (* 2.2 Sequents *)

type sequent = context * ty

let string_of_seq (c,t) = string_of_ctx c^" |- "^string_of_ty t


(* let () =
  let l = [
    "A => B";
    "A ⇒ B";
    "A /\\ B";
    "A ∧ B";
    "T";
    "A \\/ B";
    "A ∨ B";
    "_";
    "not A";
    "¬ A";
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_ty (ty_of_string s))
    ) l

    let () =
  let l = [
    "t u v";
    "fun (x : A) -> t";
    "λ (x : A) → t";
    "(t , u)";
    "fst(t)";
    "snd(t)";
    "()";
    "case t of x -> u | y -> v";
    "left(t,B)";
    "right(A,t)";
    "absurd(t,A)"
  ]
  in
  List.iter
    (fun s ->
       Printf.printf
         "the parsing of %S is %s\n%!" s (string_of_tm (tm_of_string s))
    ) l *)

let rec prove (env:(var*ty) list) a =
  print_endline (string_of_seq (env,a));
  print_string "? "; flush_all ();
  let error e = print_endline e; prove env a in
  let cmd, arg =
    let cmd = input_line stdin in
    let n = try String.index cmd ' ' with Not_found -> String.length cmd in
    let c = String.sub cmd 0 n in
    let a = String.sub cmd n (String.length cmd - n) in
    let a = String.trim a in
    c, a
  in
  match cmd with
  | "intro" ->
     (
       match a with
       | Arr (a, b) ->
          if arg = "" then error "Please provide an argument for intro." else
            let x = arg in
            let t = prove ((x,a)::env) b in
            Abs (x, a, t)
       | Conj (a, b) ->
          if arg <> "" then (print_endline("I don't need an argument for now")) else ();
          let t1 = prove env a in
          let t2 = prove env b in
          Pair (t1, t2)
        | Nat -> if arg = "zero" then Nul else if arg = "succ" then
          Succ (prove env Nat) else error "Don't know how to introduce this."
       | _ -> error "Don't know how to introduce this."
     )
  | "exact" ->
     let t = tm_of_string arg in
     if infer_type env t <> a then error "Not the right type."
     else t
  | "elim" -> (*arg is f of type A->B*)
     (let f = tm_of_string arg in
     (*see if f is of type A->B*)
      match infer_type env f with 
      | Arr(tyA,tyB) when tyB = a ->
         (*look for a term x of type A*)
         let t = prove env tyA in App(f,t)
      | Coprod(tyA,tyB) -> (let 
      t1 = prove (("fA",tyA)::env) a and t2 = prove (("fB",tyB)::env) a in
      Case(f , "fA", t1 , "fB", t2) )
      | Zero -> Case_type(f,a)
      | Nat -> 
        let t1 = (print_endline ("base case"); prove env a) (*you will have to introduce zero*)
      and t2 = (print_endline ("inductive case"); prove (("pred", Nat)::("imagepred", a)::env) a) in
      Rec(f,t1,"imagepred",t2) (*problem : when checking we need pred*)
      | _ -> error "Not the right type.") 
  | "cut" -> 
    (let b = ty_of_string arg in
    let t1 = prove env (Arr (b,a)) in
    let premise = prove env b in
    App(t1,premise)
    )
  | "fst" -> (let x = tm_of_string arg 
  in match infer_type env x with
  | Conj(ty1, _) when ty1 = a -> Fst x
  | _ -> error "Not the right type."
  )
  | "snd" -> (let x = tm_of_string arg 
  in match infer_type env x with
  | Conj(_, ty2) when ty2 = a -> Snd x
  | _ -> error "Not the right type."
  )
  | "truth_intro" -> (
    match a with 
    | TTruth -> True
    | _ -> error "Not the right type.")
  | "left" -> (match a with
    | Coprod(ty1,ty2) -> (
      let t = prove env ty1 in
      InjLeft(ty2,t))
    | _ -> error "Not the right type.")
  | "right" -> (match a with  
    | Coprod(ty1,ty2) -> (
      let t = prove env ty2 in
      InjRight(ty1,t))
    | _ -> error "Not the right type.")
  | cmd -> error ("Unknown command: " ^ cmd)
         
let () =
  print_endline "Please enter the formula to prove:";
  let a = input_line stdin in
  let a = ty_of_string a in
  print_endline "Let's prove it.";
  let t = prove [] a in
  print_endline "done.";
  print_endline "Proof term is";
  print_endline (string_of_tm t);
  print_string  "Typechecking... "; flush_all ();
  assert (infer_type [] t = a);
  print_endline "ok."


  (* cat k.proof | dune exec ./prover.exe


appid.proof: ((A => A) => B) => B *)
(* Proof term is
(fun : f : ( ( A => A ) => B ) -> ( f (fun : x : A -> x ) ) *)

(* Proof term is
(fun : f : ( A => ( B => C ) ) -> (fun : g : ( A => B ) -> (fun : x : A -> ( ( f x ) ( g x ) ) *)

(*checktype for Nat*)
let () = check_type [] (Rec(Nul, Nul, "a", Succ(Nul))) Nat

