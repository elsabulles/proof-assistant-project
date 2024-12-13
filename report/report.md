---
title: Report for the _proof assistant project_
author: Elsa Lubek
---

This is an example for the report in _Markdown_ format, which is a text format that can be converted to anything including pdf. I am fine with any other tool to produce the pdf though (Word, LaTeX, etc.). You can see the syntax at <https://pandoc.org/MANUAL.html>.

In order to produce the pdf, you should install `pandoc`, on Ubuntu this can be done with

```
sudo apt install pandoc
```

and then you can compile it to pdf by typing

```
pandoc report.md -o report.pdf
```

or simply

```
make
```

Erase the above and write an introduction.

# What was implemented in the project

Explain. You can write inline code `let x = 4`{.ocaml} or cite paragraphs of your code

```ocaml
let rec f x =
  let y = x + x in
  y * y
```

you have words in _italic_ or in **bold**.

## Simple types

...

## Dependent types



# Difficulties encountered

Detail
It was hard to catch mistakes so I added some details concerning the errors. 
For instance, at first I forgot to normalize the value when normalizing a var with a value...
I thought at first it would be easier to be not too careful at first and correct bug afterwards but eventually I think that is better to be very very careful at every step since the beginning and move forward more slowly otherwise we loose time afterwards.

In order to debug my work, I had to introduce intermediary terms for instance 'i = Ind p Z s Z'.{ocaml}. 

When I apply Ind(,,,m) to an int, should I ensure that m has no value ? Or is it ok if is has, by some rule of priority as it is the case in lambda terms... it think so

Example of bug : when I matched the reduction of m, it was a kind of comparison so I should use conv ?

I had an issue trying to prove that the successor is compatible with equality :
Typing error :Type mismatch when check that r is of type (Π fx : Nat -> (((p fx) fx) Refl (fx)))it is of type : (Π x : Nat -> ( ( S x ) = ( S x ) )).

I tried adding manier normalizations but in fact it was not useful.

I made a mistake when implementing fresh_var. Again, I had to create intermediary difficult terms to understand where the problem was coming from : define py = (((p Z) Z) (Refl Z)) for instance.
Or p Z etc.

I made a mistake, adding the value v in the context, which was creating an infinite loop (and stack overflow).

I was not sure concerning when to add the value v in the context. Il x has no value, it's normal form is Var x and it loops. So maybe I should add it only if it is not Var...

I encontered a new problem.
When trying :
define pzadd = fun (n : Nat) -> (add Z n = n)
define szadd = fun (n : Nat) -> ( fun (znz : (add Z n = n)) -> (Seq (add Z n) n znz))
define zadd = fun (n : Nat) -> (Ind pzadd Refl(Z) szadd n)
it was looping forever.
I noticed it was linked to, somewhat, S (n) = n so I renamed :
define pzadd = fun (n : Nat) -> (add Z n = n)
define szadd = fun (m : Nat) -> ( fun (znz : (add Z m = m)) -> (Seq (add Z m) m znz))
define zadd = fun (n : Nat) -> (Ind pzadd Refl(Z) szadd n)
and it worked.
But I was aware that I did not solve the real problem...
If I changed n to m in zadd, I also had an infinite loop, but changing n to m in pzadd solved the problem. So the problem was between n in p and s. They should be bounded differently and here they are mixed up.

I fixed the problem by introducing a new variable fresh_n

Show that addition is associative and commutative :

je me suis aperçue qu'il est parfois important de choisir un ordre judicieux sur les arguments. Par exemple dans cong, de prendre l'argument f avant x et y.

j'oublie souvent les "fun"

La plupart de mes problèmes viennent de quand j'utilise des fonctions/variables qui n'existent pas.

# Implementation choices

Detail
brouillons : define scommn = fun (n : Nat) -> (fun (k : Nat) -> (fun (hr : ((add k n) = (add n k)) -> )))

remove unuseful parenthesis 


# Possible extensions

Pour la symétrie de l'égalité, on pourrait faire en sorte de tester si ça marcherait dans l'autre sens et émettre la suggestion à l'utilisateur

On pourrait changer la production de fresh_var pour que ce soit avec des caractères plutôt que des nombres 

Imagine

define cong = fun (A : Type) -> (fun (x : A) -> (fun (y : A) -> fun ()) )...

On voudrait un parser moins lourd.
define pcomm' = (fun (n m : Nat) -> ( (add k n) = (add n k) ))

Ajouter des arguments implicites ce serait vraiment praqtique !!

Pour que ce soit plus joli, pouvoir mettre des commentaires (fonction comment "")

# Conclusion

Conclude
