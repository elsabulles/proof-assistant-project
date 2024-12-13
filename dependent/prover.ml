open Expr

let of_string s = Parser.expr Lexer.token (Lexing.from_string s)

let () = Printexc.record_backtrace true

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
  | Ind (p, z, s, m) -> "Ind ("^to_string(p)^", base case : "^to_string(z)^" , successor : "^to_string(s)^", applied to "^to_string(m)^")"
  | Eq (e1, e2) -> "( " ^ to_string e1 ^ " = " ^ to_string e2 ^ " )"
  | Refl e -> "Refl (" ^ to_string e ^ ")"
  | J (e1, e2, e3, e4, e5) -> "J (" ^ to_string e1 ^ ", " ^ to_string e2 ^ ", " ^ to_string e3 ^ ", " ^ to_string e4 ^ ", " ^ to_string e5 ^ ")"

  (*5.3 Fresh variable names*)

let i = ref 0
let fresh_var () = 
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
  | Abs (y, u1, u2) -> let f = fresh_var () in
  if x = y then (*x appears in the terms but is not free so we can just rename it*)
    Abs (f, subst x t u1, subst y (Var f) u2) (*car alors x ne peut pas être libre dans u2*)
  else Abs (f , (subst x t u1), (subst x t (subst y (Var f) u2)))(*problem if y is not free in t*)
  | Pi (y, u1, u2) -> let f = fresh_var () in 
  if x = y then Pi (f, subst x t u1, subst y (Var f) u2) (*not necessary, is it ?*)
  else Pi (f, subst x t (subst y (Var f) u1), subst x t (subst y (Var f) u2)) (*check again for the pb of FV...*)
  | Nat -> Nat
  | Z -> Z
  | S e -> S (subst x t e)
  | Ind (e1,e2,e3,e4) -> Ind (subst x t e1, subst x t e2, subst x t e3, subst x t e4) (*for now I think it is good*)
  | Eq (e1, e2) -> Eq (subst x t e1, subst x t e2)
  | Refl e -> Refl (subst x t e)
  | J (e1, e2, e3, e4, e5) -> J (subst x t e1, subst x t e2, subst x t e3, subst x t e4, subst x t e5)


  (* 5.5 Contexts *)

type context = (var * (expr * expr option)) list

let rec string_of_context c = 
  match c with 
  | [] -> ""
  | (x, (a,t))::q when t=None -> x^" : "^(to_string a)^"\n"^(string_of_context q)
  | (x, (a,Some v))::q -> x^" : "^to_string a^" = "^(to_string v)^"\n"^(string_of_context q)
  |_ -> failwith ("? is that a context ?")

(*the function prints the beginning of the ctx*)
let str_beginning_context ctx = 
  let s = ref "" in
let ind = ref 0 in
  while (ctx <> [] && (!ind < 5)) do
    match (List.nth ctx !ind) with
    | (x, (a,Some v)) ->  s := !s^x^" : "^to_string a^" = "^(to_string v)^"\n";
    | (x, (a,None)) ->  s := !s^x^" : "^(to_string a)^"\n";
    ind := !ind + 1;
  done;
  !s^"..."

(* 5.6 Normalization *)
let rec normalize ctx e = 
  match e with
  | Type -> e
  | Var x -> (try (match (List.assoc x ctx) with 
                  | _, Some v when v=e -> failwith (to_string(e)^" has value itself")
                  | _, Some v  -> (normalize ctx v) 
                  | _, None -> e )
             with |Not_found -> failwith (x^" is not defined in"^string_of_context(ctx)))
  | App (u1, u2) -> 
   (match (normalize ctx u1),(normalize ctx u2) with
   (*in comments th eprevious version*)
   (*I try adding the value only if it is relevant in order to avoid loopings*)
    | Abs (x, a, b), Var v -> subst x (Var v) (normalize ((x, (a,None))::ctx) b) 
    | Pi (x, a, b), Var v -> subst x (Var v) (normalize ((x, (a,None))::ctx) b) 
    | Abs (x, a, b),v -> subst x v (normalize ((x, (a,Some v))::ctx) b)
    | Pi (x, a, b),v -> subst x v (normalize ((x, (a,Some v))::ctx) b) (*LOOPING ?*)
    | val1,val2 -> App (val1 , val2)
    )
  | Pi (x, a, b) -> Pi (x, normalize ctx a, normalize ((x,(a,None))::ctx) b)
  | Nat -> Nat
  | Z -> Z
  | Abs (x, a, b) -> Abs (x, normalize ctx a, normalize ((x,(a,None))::ctx) b)
  | S (ex) -> S (normalize ctx ex)
  (*maybe I should reconsider normalisation*)
  | Ind (p,z,s,u) -> (match (normalize ctx u) with
      | Z -> z
      | S (n) -> normalize ctx (App( App( s, n) , (Ind (p, z, s, n))))
      | u_norm -> (*print_endline(to_string(u_norm)^" is not Z nor S(n)"); *) Ind (normalize ctx p, normalize ctx z, normalize ctx s, u_norm))
  | Eq (e1, e2) -> Eq (normalize ctx e1, normalize ctx e2)
  | Refl e -> Refl (normalize ctx e)
  | J (p, r, x, y, eg) -> (let x' = (normalize ctx x) in 
  match (normalize ctx y), (normalize ctx eg) with 
  | y', Refl (z) when x'=y' && x'=z -> normalize ctx (App(r,x'))
  | _,_ -> J (normalize ctx p, normalize ctx r, normalize ctx x, normalize ctx y, normalize ctx eg)
  )

(*test*)
(* let () = print_endline(string_of_context [("x", (Type, None))])
let ()= print_endline(string_of_context [("x", (Type, Some Z))]) *)

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
| Ind (e1,e2,e3,e4), Ind (f1,f2,f3,f4) -> (alpha e1 f1)&&(alpha e2 f2)&&(alpha e3 f3)&&(alpha e4 f4)
| Eq (e1, e2), Eq (f1, f2) -> (alpha e1 f1)&&(alpha e2 f2)
| Refl e, Refl f -> alpha e f
| J (e1,e2,e3,e4,e5), J (f1,f2,f3,f4,f5) -> alpha e1 f1 && alpha e2 f2 && alpha e3 f3 && alpha e4 f4 && alpha e5 f5
| _ -> false


(* 5.8 Conversion *)

let conv ctx t1 t2 =
  alpha (normalize ctx t1) (normalize ctx t2)

  (* 5.9 Type inference and 5.10 Type checking*)

exception Type_error of string

(* infers the type of e in the context ctx *)
(*But we need to check that the context is*)
(*corresponds to elimination ?*)
let rec infer ctx e = match e with
| Type -> Type (*REALLY ?*)
| Var v -> (try (fst (List.assoc v ctx)) with | Not_found -> raise (Type_error ("v is not defined in"^str_beginning_context(ctx))))
| App (e1, e2) -> (match (infer ctx e1) with 
            | Pi(v,x,y) -> check ctx e2 x; subst v e2 y (*is normalization necessary ?*)
            | _ -> match (normalize ctx e1) with 
              | Pi(x,a,b) -> check ctx e2 a; subst x e2 b 
            (* infer ((v,(x,Some e2))::ctx) y *)
           (*what if e1 was a pi ?*)
              | other -> raise(Type_error(to_string(other)^" is not a function type when inferring the type")) ) (*should we change the context ?*)
| Abs (x,a,t) -> check ctx a Type; Pi (x,a,infer ((x, (a,None))::ctx) t)
| Pi (x, a, b) -> check ctx a Type; check ((x, (a,None))::ctx) b Type; Type
| Nat -> Type
| Z -> Nat
| S(e) -> (try (check ctx e Nat) with |_ -> raise (Type_error("Successor should take an int"))); Nat
(* | Ind (t,xA,u,xyv) -> check ctx t Nat; let x = fresh_var and y = fresh_var in
 let a = infer ((x , (Nat, None))::ctx) (App(xA, Var x)) in let typ_v = infer ((y , (a, None))::(x , (Nat, None))::ctx) (App (App(xyv, Var x) , Var y)) in
 check u (subst x Z a); check typ_v  *)
 | Ind (p, z, s, m) -> (check ctx z (App(p, Z)); print_endline("base case well typed");
 (* then (raise (Type_error"base case is not of a type p Z")) else (  if there is no mistake p is of type Nat => Type ? *)
  match infer ctx s with 
    | Pi (n, Nat, f) -> (*let's try*) print_endline(to_string(f)^" is f");
    let fresh_n = fresh_var () in
    let pn = normalize ((fresh_n , (Nat, None))::ctx) (App(p,Var fresh_n))in print_endline(to_string(pn)^" is the type of p n");
    let pSn = normalize ((fresh_n , (Nat, None))::ctx) (App(p, S (Var fresh_n))) in print_endline(to_string(pSn)^" is the type of p (S n) ");
    if (conv ((fresh_n , (Nat, None))::ctx) (subst n (Var fresh_n) f) (Pi("x", pn, pSn))) then (
      print_endline(to_string(f)^" is of good type...");
    (*the problem here is that I need to add n of type nat to f but not to p. So I cannot use conv which requires the same *)
    (check ctx m Nat; normalize ctx (App(p,m))) (*should we normalize ?*)
     )
     else raise(Type_error(to_string(s)^"is not a function")); 
  (*i'm not sure about the "x" part*)
    | _ -> raise (Type_error("Your recursor is not well typed")) 
 ) 
 | Refl(t) -> let t' = normalize ctx t in Eq (t',t') (*I don't think I have to normalize now*)
 | Eq (e1,e2) -> check ctx e1 (infer ctx e2); Type
 | J (p,r,x,y,eg) -> (
  (*define A*) let a = infer ctx x in
  check ctx y a;
  check ctx eg (Eq(x,y)); (*should I normalize ? or check does it?*)
  let fx, fy, fz = fresh_var (), fresh_var (), fresh_var () in  (*A CHANGER APRES*)
  check ctx p (Pi(fx,a,Pi(fy,a,Pi(fz,Eq (Var fx,Var fy),Type)))); (*pb...?*)
  check ctx r (Pi(fx,a,App(App(App(p,Var fx),Var fx),Refl (Var fx))));
  normalize ctx (App(App(App(p,x),y),eg)) (*I TRY NORMALIZING*)
 )

(*use conv*)
and check ctx e t = 
if conv ctx (infer ctx e) t then () else raise(Type_error("Type mismatch when check that "^to_string(e)^" is of type "^to_string(t)^"it is of type : "^to_string(infer ctx e))) 

let () =
  let env = ref [] in
  let loop = ref true in
  let file = open_out "interactive.proof" in
  let split c s =
    try
      let n = String.index s c in
      String.trim (String.sub s 0 n), String.trim (String.sub s (n+1) (String.length s - (n+1)))
    with Not_found -> s, ""
  in
  while !loop do
    try
      print_string "? ";
      flush_all ();
      let cmd, arg =
        let cmd = input_line stdin in
        output_string file (cmd^"\n");
        print_endline cmd;
        split ' ' cmd
      in
      match cmd with
      | "assume" ->
        let x, sa = split ':' arg in
        let a = of_string sa in
        check !env a Type;
        env := (x,(a,None)) :: !env;
        print_endline (x^" assumed of type "^to_string a)
      | "define" ->
        let x, st = split '=' arg in
        let t = of_string st in
        let a = infer !env t in
        env := (x,(a,Some t)) :: !env;
        print_endline (x^" defined to "^to_string t^" of type "^to_string a)
      | "context" ->
        print_endline (string_of_context !env)
      | "type" ->
        let t = of_string arg in
        let a = infer !env t in
        print_endline (to_string t^" is of type "^to_string a)
      | "check" ->
        let t, a = split '=' arg in
        let t = of_string t in
        let a = of_string a in
        check !env t a;
        print_endline "Ok."
      | "eval" ->
        let t = of_string arg in
        let _ = infer !env t in
        (* print_endline("let's normalize "^to_string(t)^" in context : \n"^(string_of_context !env)^"\n"); *)
        print_endline (to_string (normalize !env t))
      | "exit" -> loop := false
      | "" | "#" -> ()
      | cmd -> print_endline ("Unknown command: "^cmd)
    with
    | End_of_file -> loop := false
    | Failure err -> print_endline ("Error: "^err^".")
    | Type_error err -> print_endline ("Typing error :"^err^".")
    | Parsing.Parse_error -> print_endline ("Parsing error.")
  done;
  print_endline "Bye."