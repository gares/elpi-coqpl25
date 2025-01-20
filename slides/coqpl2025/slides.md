---
# You can also start simply with 'default'
theme: neversink
color: rocq
# random image from a curated Unsplash collection by Anthony
# like them? see https://unsplash.com/collections/94734566/slidev
# background: https://cover.sli.dev
# some information about your slides (markdown enabled)
title: Elpi rule-based meta-languge for Rocq
info: |
  ## Slidev Starter Template
  Presentation slides for developers.

  Learn more at [Sli.dev](https://sli.dev)
# apply unocss classes to the current slide
class: text-center
# https://sli.dev/features/drawing
drawings:
  persist: false
# slide transition: https://sli.dev/guide/animations.html#slide-transitions
# enable MDC Syntax: https://sli.dev/features/mdc
mdc: true
layout: cover
image: logo.png
transition: fade
level: 2
hideInToc: true
---

# Elpi: rule-based meta-languge for Rocq

Enrico Tassi<sup>1</sup> - CoqPL 2025

<div class="flex justify-center items-center">

<div>

![Elpi logo](/logo.png "Logo")

</div>

</div>

:: note ::
1 Inria Centre at Université Côte d’Azur 

---
layout: center
level: 2
---

# This talk
<br/>

<Toc minDepth="1" maxDepth="1" />

<!--
First of all thanks the orga
-->

---
layout: section
color: rocq
---

# Users of Elpi

- https://github.com/math-comp/hierarchy-builder/
- https://github.com/coq-community/trocq
- https://github.com/LPCIC/coq-elpi/tree/master/apps/derive
- https://github.com/math-comp/algebra-tactics/

---
layout: two-cols-header
level: 2
---

# Hierarchy Builder

<div class="authors">

![CohenCyril](/avatars/CohenCyril.jpg)
![pi8027](/avatars/pi8027.jpg)
![gares](/avatars/gares.jpg)
![proux01](/avatars/proux01.jpg)
![ThomasPortet](/avatars/ThomasPortet.jpg)
![affeldt-aist](/avatars/affeldt-aist.jpg)
<!--
![FissoreD](/avatars/FissoreD.jpg)
![SkySkimmer](/avatars/SkySkimmer.jpg)
![thery](/avatars/thery.jpg)
![Tvallejos](/avatars/Tvallejos.jpg)
![VojtechStep](/avatars/VojtechStep.jpg)
![ybertot](/avatars/ybertot.jpg)
-->

</div>

DSL to declare a hierarchy of interfaces

:: left ::

* generates boilerplate via Elpi's API: modules, implicit arguments, canonical structures, ... 
* used by the Mathematical Components library and other ~20 libraries
* makes "packed classes" easy

  ![MC](/hb_intf.png "number of interfaces"){style="width: 80%"}

  2017
  <span style="width:8em; display:inline-block"/>
  2022
  <span style="width:2em; display:inline-block"/>
  2024

:: right ::

```coq
From HB Require Import structures.

HB.mixin Record IsAddComoid A := {
  zero : A;
  add : A -> A -> A;
  addrA : forall x y z, add x (add y z) = add (add x y) z;
  addrC : forall x y, add x y = add y x;
  add0r : forall x, add zero x = x;
}.

HB.structure Definition AddComoid := { A of IsAddComoid A }.

Notation "0" := zero.
Infix "+" := add.

Check forall (M : AddComoid.type) (x : M), x + x = 0.
```

<!--
this is the command / this is the argument

uses the APIs to declare modules, coercions, implicit arguments
-->

---
layout: two-cols-header
level: 2
---

# Trocq

<div class="authors">

![ecranceMERCE](/avatars/ecranceMERCE.jpg)
![amahboubi](/avatars/amahboubi.jpg)
![CohenCyril](/avatars/CohenCyril.jpg)
<!-- ![palmskog](/avatars/palmskog.jpg) -->

</div>

Proof transfer via parametricity (with or without univalence).

:: left ::

<div style="padding-right: 3em">


- Registers in Elpi Databases translation rules
- Synthesizes transfer proofs minimizing the axioms required

</div>

:: right :: 

<div style="transform: scale(1.2)">

```coq 
From Trocq Require Import Trocq.

Definition RN : (N <=> nat)%P := ...
Trocq Use RN.

Lemma RN0 : RN 0%N 0%nat. ...
Lemma RNS m n : RN m n -> RN (N.succ m) (S n). ...
Trocq Use RN0 RNS.

Lemma N_Srec : ∀P : N -> Type, P 0%N ->
    (∀n, P n -> P (N.succ n)) -> ∀n, P n.
Proof.
trocq. (* replaces N by nat in the goal *)
exact nat_rect.
Qed.
```

</div>

---
layout: two-cols-header
level: 2
---

# Derive

<div class="authors">

![gares](/avatars/gares.jpg)
![CohenCyril](/avatars/CohenCyril.jpg)
![bgregoir](/avatars/bgregoir.jpg)
![eponier](/avatars/eponier.jpg)
![Blaisorblade](/avatars/Blaisorblade.jpg)
![rlepigre](/avatars/rlepigre.jpg)
![dwarfmaster](/avatars/dwarfmaster.jpg)
<!--
![artagnon](/avatars/artagnon.jpg)
![ecranceMERCE](/avatars/ecranceMERCE.jpg)
![ejgallego](/avatars/ejgallego.jpg)
![FissoreD](/avatars/FissoreD.jpg)
![herbelin](/avatars/herbelin.jpg)
![jfehrle](/avatars/jfehrle.jpg)
![maximedenes](/avatars/maximedenes.jpg)
![pedrotst](/avatars/pedrotst.jpg)
![phikal](/avatars/phikal.jpg)
![pi8027](/avatars/pi8027.jpg)
![ppedrot](/avatars/ppedrot.jpg)
![proux01](/avatars/proux01.jpg)
![robblanco](/avatars/robblanco.jpg)
![SimonBoulier](/avatars/SimonBoulier.jpg)
![SkySkimmer](/avatars/SkySkimmer.jpg)
![Tragicus](/avatars/Tragicus.jpg)
![vbgl](/avatars/vbgl.jpg)
![VojtechStep](/avatars/VojtechStep.jpg)
![wdeweijer](/avatars/wdeweijer.jpg)
![whonore](/avatars/whonore.jpg)
![ybertot](/avatars/ybertot.jpg)
![yoichi-at-bedrock](/avatars/yoichi-at-bedrock.jpg)
![Zimmi48](/avatars/Zimmi48.jpg)
-->

</div>

Framework for type driven code synthesis

:: left ::

<div style="padding-right: 3em">

Derivations:
- parametricity
- deep induction
- equality tests and proofs
- lenses (record update syntax)
- a few more...

</div>

:: right :: 

<div style="transform: scale(1.2)">

```coq
From elpi.apps Require Import derive.std lens.

#[only(lens_laws, eqb), module] derive
Record Box A := { contents : A; tag : nat }.

About Box. (* Notation Box := Box.t *)

Check Box.eqb :
  ∀A, (A -> A -> bool) -> Box A -> Box A -> bool.

(* the Lens for the second field *)
Check @Box._tag : ∀A, Lens (Box A) (Box A) nat nat.

(* a Lens law *)
Check Box._tag_set_set : ∀A (r : Box A) y x,
  set Box._tag x (set Box._tag y r) = set Box._tag x r.
```

</div>


---
layout: two-cols-header
level: 2
---

# Algebra Tactics

<div class="authors">

![pi8027](/avatars/pi8027.jpg)
![proux01](/avatars/proux01.jpg)
![amahboubi](/avatars/amahboubi.jpg)
<!-- ![CohenCyril](/avatars/CohenCyril.jpg)
![gares](/avatars/gares.jpg) -->

</div>

`ring`, `field`, `lra`, `nra`, and `psatz` tactics for the Mathematical Components library. 

:: left ::

- works with any instance of the structure: concrete, abstract and mixed
  like `int * R` where `R` is a variable
- automatically push down ring morphisms and additive functions to
  leaves of the expression
- reification up to instance unification in Elpi


:: right ::

```coq
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ring lra.

Lemma test (F : realFieldType) (x y : F) :
  x + 2 * y <= 3 ->
  2 * x + y <= 3 ->
    x + y <= 2.
Proof. lra. Qed.

Variables (R : unitRingType) (x1 x2 x3 y1 y2 y3 : R).
Definition f1 : R := ...
Definition f2 : R := ...
Definition f3 : R := ...

(* 500 lines of polynomials later... *)

Lemma example_from_Sander : f1 * f2 = f3.
Proof. rewrite /f1 /f2 /f3. ring. Qed.
```


---
layout: section
color: rocq
---

# Elpi in a nutshell

https://github.com/LPCIC/elpi/

---
layout: two-cols-header
image: vespa.png
backgroundSize: 80%
level: 2
---

# Rules, rules, rules!{style="text-align:center"}


:: left ::


## Roots

- Elpi is a constraint logic programming language
- Elpi is a dialect of λProlog and CHR
- backtracking is not the point

<br/>

## What really matters

- Code is organized in rules
- Rule application is guided by a pattern
- Rules can be added statically and dynamically



:: right ::

## <icon-park-twotone-caution/> Vintage syntax ahead

<ul>
<li><p>variables are capitals
<force-inline>
```elpi
X
```
</force-inline>
</p></li>

<li><p> λx.t  is written
<force-inline>
```elpi
x\ t
```
</force-inline>
</p></li>

<li><p>rules are written
<force-inline>
```elpi
goal :- subgoal1, subgoal2...
```
</force-inline>
</p></li>

</ul>


---
layout: two-cols-header
level: 2
---

# Elpi: Hello World!

::left::

Simply typed $\lambda$-calculus in HOAS

<<< @/snippets/stlc.elpi#types elpi

Typing


````md magic-move

<<< @/snippets/stlc.elpi#of elpi
<<< @/snippets/stlc.elpi#of1 elpi
<<< @/snippets/stlc.elpi#of2 elpi
<<< @/snippets/stlc.elpi#of elpi


````

::right::

````md magic-move {at:1}

```elpi
goal> of (lam x\ lam y\ x) TyFst.
```

```elpi
goal> of (lam x\ lam y\ x) (arr S0 T0).
goal> of        (lam y\ c) T0.
```

```elpi
goal> of (lam x\ lam y\ x) (arr S0 (arr S1 T1)).
goal> of        (lam y\ c) (arr S1 T1).
goal> of                c  T1.
```

```elpi
goal> of (lam x\ lam y\ x) TyFst.

Success:
  TyFst = arr S0 (arr S1 S0)
```

```elpi
goal> of (app H A) T.

Failure.
```

````

---
layout: two-cols-header
level: 2
---

# Elpi = $\lambda$Prolog + CHR

::left::

Typing (as before)

<<< @/snippets/stlc.elpi#of elpi

Holes & constraints

<<< @/snippets/stlc.elpi#cst elpi

<v-click at="6">
Constraint Handling Rules

<<< @/snippets/stlc.elpi#chr elpi
</v-click>

::right::

````md magic-move
```elpi
goal> of (app H A) T.
```

```elpi
goal> of (app H A) T.

Success:

Constraints:
  of A S  /* suspended on A */
  of H (arr S T)  /* suspended on H */
```

```elpi
goal> of (app H A) T, H = (lam x\ x).

Success:

Constraints:
  of A T  /* suspended on A */
```

```elpi
goal> of (app (lam x\ x) A) T.

Success:

Constraints:
  of A T  /* suspended on A */
```

```elpi
goal> of (app D D) T.
```

```elpi
goal> of (app D D) T.

Success:

Constraints:
  of D S  /* suspended on D */
  of D (arr S T)  /* suspended on D */
```

```elpi
goal> of (app D D) T.

Failure
```
````


---
layout: section
color: rocq
transition: fade
---

# Integration in Rocq

https://github.com/LPCIC/coq-elpi/

---
layout: image-right
image: readme.png
backgroundSize: 80%
transition: fade
level: 2
---

# Notable features

- HOAS for Gallina
- quotations and anti-quotations

  ![Quotations](/quote.png "quote")

- Databases of rules
- Extensive API

  ![API example](/api.png "api")

---
layout: two-cols-header
transition: fade
level: 2
---

# Demo: from Prop to bool

:: left ::

```coq
Axiom is_even : nat -> Prop.

Fixpoint even n : bool := match n with
  | O => true
  | S (S n) => even n
  | _ => false
  end.

Lemma evenP n : reflect (is_even n) (even n).
(* Elpi add_tb evenP. *)

Lemma andP  {P Q : Prop} {p q : bool} :
  reflect P p -> reflect Q q ->
    reflect (P /\ Q) (p && q).
(* Elpi add_tb andP. *)

Lemma elimT {P b} : reflect P b -> b = true -> P.
```

```coq
Lemma test : is_even 6 /\ is_even 4.
Proof.
  refine (elimT (andP (evenP 6) (evenP 4)) _).
  (* elpi to_bool. *)
  simpl. trivial.
Qed.
```

:: right ::

````md magic-move

```coq
(* [tb P R] finds R : reflect P _ *)
Elpi Tactic to_bool.
Elpi Accumulate lp:{{
  pred tb i:term, o:term.
  tb {{ is_even lp:N }} {{ evenP lp:N }}.
  tb {{ lp:P /\ lp:Q }} {{ andP lp:PP lp:QQ }} :- tb P PP, tb Q QQ.

  solve (goal _ _ Ty _ _ as G) GL :-
    tb Ty P, refine {{ elimT lp:P _ }} G GL.              }}.
```

```coq
(* [tb P R] finds R : reflect P _ *)
Elpi Db tb.db lp:{{ pred tb i:term, o:term. }}.

Elpi Tactic to_bool.
Elpi Accumulate Db tb.db.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ _ as G) GL :-
    tb Ty P, refine {{ elimT lp:P _ }} G GL.              }}.

Elpi Command add_tb.
Elpi Accumulate Db tb.db.
Elpi Accumulate lp:{{
  pred compile i:term, i:term, i:list prop, o:prop.
  compile {{ reflect lp:P _ }} R Todo (tb P R :- Todo).
  compile {{ reflect lp:S _ -> lp:Ty }} R Todo (pi h\C h) :-
    pi h\ compile Ty {coq.mk-app R [h]} [tb S h|Todo] (C h).
  compile {{ forall x, lp:(Ty x) }} R Todo (pi x\ C x) :-
    pi x\ compile (Ty x) {coq.mk-app R [x]} Todo (C x).

  main [str S] :-
    coq.locate S GR,
    coq.env.typeof GR Ty,
    compile Ty (global GR) [] C,
    coq.elpi.accumulate _ "tb.db" (clause _ _ C).        }}.

```

````

---
layout: section
color: rocq
---

# The good company

https://github.com/coq-community/metaprogramming-rosetta-stone

---
transition: fade
zoom: 0.85
level: 2
---

# Comparison

<table>

<thead>
<tr style="border-bottom-width: 4px"> <th></th> <th>Elpi</th> <th>Ltac2</th> <th>MetaCoq</th> </tr>
</thead>
<tbody>

<tr> <td>Gallina</td>
  <td>
    <icon-park-twotone-pie-seven/>
    <br/><small>no mutual fix/ind</small>
  </td>
  <td>
    <icon-park-twotone-round/>
  </td>
  <td>
    <icon-park-twotone-round/>
  </td>
</tr>

<tr> <td>Bound Variables</td>
  <td>
    <icon-park-twotone-round/>
  </td>
  <td>
    <icon-park-twotone-pie-three/>
    <br/><small>quotations</small>

  </td>
  <td>
    <icon-park-twotone-pie-one/>
    <br/><small>toplevel quotation</small>
  </td>
</tr>

<tr style="border-bottom-width: 4px"> <td>Holes</td>
  <td>
    <icon-park-twotone-round/>
  </td>
  <td>
    <icon-park-twotone-pie-five/>
    <br/><small>tactic monad</small>

  </td>
  <td>
    <icon-park-twotone-pie-one/>
    <br/><small>only AST</small>
  </td>
</tr>

<tr> <td>Proof API</td>
  <td>
    <icon-park-twotone-pie-four/>
    <br/><small>weak ltac1 bridge</small>
  </td>
  <td>
    <icon-park-twotone-round/>
    <br/><small>(sufficiently close)</small>
  </td>
  <td>
    <icon-park-twotone-pie-one/>
    <br/><small>only TC search, obligations</small>
  </td>
</tr>

<tr style="border-bottom-width: 4px"> <td>Vernacular API</td>
  <td>
    <icon-park-twotone-pie-seven/>
    <br/><small>no notations, obligations</small>
  </td>
  <td>
    <material-symbols-circle-outline/>
  </td>
  <td>
    <icon-park-twotone-pie-three/>
    <br/><small>only env, obligations</small>
  </td>
</tr>

<tr style="border-bottom-width: 4px"> <td>Reasoning logic</td>
  <td>
    <icon-park-twotone-pie-one/>
    <br/><small>Abella</small>
  </td>
  <td>
    <material-symbols-circle-outline/>
  </td>
  <td>
    <icon-park-twotone-pie-six/>
    <br/><small>no holes, unif</small>
  </td>
</tr>

</tbody>
</table>

To the best of my knowledge, on 1/1/2025 {style="text-align:center"}

<!--

| | Elpi | Ltac2 | MetaCoq |
|--|:--:|--|--|
| Gallina         | <icon-park-twotone-pie-seven/><br/> cofix/mutind               | <icon-park-twotone-round/>                      | <icon-park-twotone-round/> |
| Bound Variables | <icon-park-twotone-round/>                 | <icon-park-twotone-pie-three/> | <icon-park-twotone-pie-one/>
| Holes (evars)   | <icon-park-twotone-round/>                 | <icon-park-twotone-pie-five/> | <icon-park-twotone-pie-one/> |
| Quotations | <carbon-thunderstorm/> | <carbon-sun/> |
| Vernacular API | |  |
| Tactic API | <Thumb width="1em"/> |
| Reasoning |  <icon-park-twotone-pie-two/><sup>2</sup> | <material-symbols-circle-outline/> |  <icon-park-twotone-round/> |
-->

---
layout: section
color: rocq
---

# Conclusion

---
layout: default
level: 2
---

# Elpi for Rocq: take home

<br/>

## Extension language
  - Use a language (ony) when it is a good fit
  - Good FFI -> many APIs!
  
## Rule-based is a good fit for
  - HOAS (binders and local context)
  - prover logical environment (global context)
  - (meta) meta programming (homoiconicity)


---
layout: default
level: 2
---

# Ongoing and future work on Rocq-Elpi

- Type Class solver (D.Fissore PhD)
- Obligations (commands that start a proof)
- Mutual fixpoints and inductives (needed by 2 power users)

# Ongoing and future work on Elpi

- Mode and determinacy analysis
- Memoization (tabling)

---
layout: two-cols-header
image: logo.png
backgroundSize: 80%
level: 2
title: Thanks
---

# Thanks! {style="text-align:center"}

# Questions? {style="text-align:center; position: absolute; bottom: 1em; left:43%; display: block"}

:: right ::

<div class="vauthors">

<div style="text-align:center">

https://github.com/LPCIC/coq-elpi/

</div>
<br/>

![Armael](/avatars/Armael.jpg)
![artagnon](/avatars/artagnon.jpg)
![bgregoir](/avatars/bgregoir.jpg)
![Blaisorblade](/avatars/Blaisorblade.jpg)
![cdunchev](/avatars/cdunchev.jpg)
![CohenCyril](/avatars/CohenCyril.jpg)
![dwarfmaster](/avatars/dwarfmaster.jpg)
![ecranceMERCE](/avatars/ecranceMERCE.jpg)
![ejgallego](/avatars/ejgallego.jpg)
![eponier](/avatars/eponier.jpg)
![FissoreD](/avatars/FissoreD.jpg)
<!-- ![gares](/avatars/gares.jpg) -->
![gdufrc](/avatars/gdufrc.jpg)
![herbelin](/avatars/herbelin.jpg)
![jfehrle](/avatars/jfehrle.jpg)
![jwintz](/avatars/jwintz.jpg)
![kit-ty-kate](/avatars/kit-ty-kate.jpg)
![lthls](/avatars/lthls.jpg)
![lukovdm](/avatars/lukovdm.jpg)
![maximedenes](/avatars/maximedenes.jpg)
![mb64](/avatars/mb64.jpg)
![MSoegtropIMC](/avatars/MSoegtropIMC.jpg)
![palmskog](/avatars/palmskog.jpg)
![pedrotst](/avatars/pedrotst.jpg)
![phikal](/avatars/phikal.jpg)
![pi8027](/avatars/pi8027.jpg)
![ppedrot](/avatars/ppedrot.jpg)
![proux01](/avatars/proux01.jpg)
![rgrinberg](/avatars/rgrinberg.jpg)
![rlepigre](/avatars/rlepigre.jpg)
![robblanco](/avatars/robblanco.jpg)
![sacerdot](/avatars/sacerdot.jpg)
![shonfeder](/avatars/shonfeder.jpg)
![SimonBoulier](/avatars/SimonBoulier.jpg)
![SkySkimmer](/avatars/SkySkimmer.jpg)
![smuenzel](/avatars/smuenzel.jpg)
![Tragicus](/avatars/Tragicus.jpg)
![vbgl](/avatars/vbgl.jpg)
![VojtechStep](/avatars/VojtechStep.jpg)
![voodoos](/avatars/voodoos.jpg)
![wdeweijer](/avatars/wdeweijer.jpg)
![whonore](/avatars/whonore.jpg)
![XVilka](/avatars/XVilka.jpg)
![ybertot](/avatars/ybertot.jpg)
![yoichi-at-bedrock](/avatars/yoichi-at-bedrock.jpg)
![Zimmi48](/avatars/Zimmi48.jpg)

</div>

<br/>

:: left ::

<!--![logo](/logo.png){style="width:40%; margin-left:auto; margin-right: auto;"}-->

<div style="text-align:justify">

For having invited me, for listening, and for **contributing** code:
<br/><br/>
Pedro Abreu, Yves Bertot, Frederic Besson, Rob Blanco, Simon Boulier, Luc Chabassier, Cyril Cohen, Enzo Crance, Maxime Dénès, Jim Fehrle, Davide Fissore, Paolo G. Giarrusso, Gaëtan Gilbert, Benjamin Gregoire, Hugo Herbelin, Yoichi Hirai, Jasper Hugunin, Emilio Jesus Gallego Arias, Jan-Oliver Kaiser, Philip Kaludercic, Chantal Keller, Vincent Laporte, Jean-Christophe Léchenet, Rodolphe Lepigre, Karl Palmskog, Pierre-Marie Pédrot, Ramkumar Ramachandra, Pierre Roux, Pierre Roux, Claudio Sacerdoti Coen, Kazuhiko Sakaguchi, Matthieu Sozeau, Gordon Stewart, David Swasey, Alexey Trilis, Quentin Vermande, Théo Zimmermann, wdewe, whonore 

</div>
