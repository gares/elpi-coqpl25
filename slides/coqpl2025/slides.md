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


DSL to declare a hierarchy of interfaces

:: left ::

* generates boilerplate via Elpi's API: modules, implicit arguments, canonical structures, ... 
* used by the Mathematical Components library and other ~20 libraries
* makes "packed classes" easy ('17, '22, '24)

  ![MC](/hb_intf.png "number of interfaces"){style="width: 80%"}


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

---
layout: two-cols-header
level: 2
---

# Trocq

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

Framework for type drive code synthesis

:: left ::

<div style="padding-right: 3em">

- parametricity
- deep induction
- equality tests and proofs
- lenses (record update syntax)

</div>

:: right :: 

<div style="transform: scale(1.2)">

```coq
From elpi.apps Require Import derive.std lens.

#[verbose, only(lens_laws, eqb), module] derive
Record Box A := { contents : A; tag : nat }.

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

Ring, field, lra, nra, and psatz tactics for the Mathematical Components library. 

:: left ::

- works with any instance of the structure: concrete, abstract and mixed
  int * R where R is a variable
- automatically push down ring morphisms and additive functions to
  leaves of ring/field expressions before applying the proof procedures
- reification up to instance unification in Elpi


:: right ::

```coq
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import lra.

Local Open Scope ring_scope.

Lemma test (F : realFieldType) (x y : F) :
  x + 2%:R * y <= 3%:R ->
  2%:R * x + y <= 3%:R ->
    x + y <= 2%:R.
Proof. lra. Qed.

Variables (R : unitRingType).
Definition f1 := ...
Definition f2 := ...
Definition f3 := ...
(* 500 lines later *)
Lemma from_sander : f1 * f2 = f3.
Proof. rewrite /f1 /f2 /f3. ring. Qed.
```


---
layout: section
color: rocq
---

# Elpi in a nutshell

https://github.com/LPCIC/elpi/

---
layout: image-right
image: vespa.png
backgroundSize: 80%
level: 2
---

# Rules, rules, rules!

- Code is organized in rules
- Rule application is guided by a pattern
- Rules can be added statically and dynamically

(Yes, Elpi is a logic programming language)

### <icon-park-twotone-caution/> vintage syntax ahead

<ul>
<li><p>variables are capitals
<force-inline>
```elpi
X
```
</force-inline>
</p></li>

<li><p> λx.t  is 
<force-inline>
```elpi
x\ t
```
</force-inline>
</p></li>

<li><p>rules are like
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

```
goal> of (lam x\ lam y\ x) TyFst.
```

```
goal> of (lam x\ lam y\ x) (arr X0 T).
goal> of        (lam y\ c) T.
```

```
goal> of (lam x\ lam y\ x) (arr X0 (arr X1 T')).
goal> of        (lam y\ c) (arr X1 T').
goal> of                c  T'.
```

```
goal> of (lam x\ lam y\ x) TyFst.

Success:
  TyFst = arr X0 (arr X1 X0)
```

```
goal> of (app H A) T.

Failure.
```

````

---
layout: two-cols-header
level: 2
---

# Elpi: $\lambda$Prolog + CHR

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
```
goal> of (app H A) T.
```

```
goal> of (app H A) T.

Success:
  A = X0
  H = X1
  T = X2

Constraints:
  of X0 X3  /* suspended on X0 */
  of X1 (arr X3 X2)  /* suspended on X1 */
```

```
goal> of (app H A) T, H = (lam x\ x).

Success:
  A = X0
  H = lam c0 \ c0
  T = X1

Constraints:
  of X0 X1  /* suspended on X0 */
```

```
goal> of (app (lam x\ x) A) T.

Success:
  A = X0
  T = X1

Constraints:
  of X0 X1  /* suspended on X0 */
```

```
goal> of (app D D) _.
```

```
goal> of (app D D) _.

Success:
  D = X0

Constraints:
  of X0 X1  /* suspended on X0 */
  of X0 (arr X1 X2)  /* suspended on X0 */
```

```
goal> of (app D D) _.

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

# Demo xP

:: left ::

<<< @/snippets/xP.v#to_bool coq

:: right ::

<<< @/snippets/xP.v coq


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
    <br/><small>only env, obligation</small>
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

# Elpi

- Mode and determinacy analysis
- Memoization (tabling)

# Rocq-Elpi

- Type Class solver
- Mutual fixpoints and inductives
- Obligations

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

![Homepage](/frame.png "qrcode"){style="width: 60%; margin-left:auto; margin-right: auto;"}

<span style="text-align:center">

https://github.com/LPCIC/coq-elpi/

</span>

<br/>

:: left ::

<!--![logo](/logo.png){style="width:40%; margin-left:auto; margin-right: auto;"}-->

For having invited me, for listening, and for **contributing code**:<br/>
Pedro Abreu, Yves Bertot, Frederic Besson, Rob Blanco, Simon Boulier, Luc Chabassier, Cyril Cohen, Enzo Crance, Maxime Dénès, Jim Fehrle, Davide Fissore, Paolo G. Giarrusso, Gaëtan Gilbert, Benjamin Gregoire, Hugo Herbelin, Yoichi Hirai, Jasper Hugunin, Emilio Jesus Gallego Arias, Jan-Oliver Kaiser, Philip Kaludercic, Chantal Keller, Vincent Laporte, Jean-Christophe Léchenet, Rodolphe Lepigre, Karl Palmskog, Pierre-Marie Pédrot, Ramkumar Ramachandra, Pierre Roux, Pierre Roux, Claudio Sacerdoti Coen, Kazuhiko Sakaguchi, Matthieu Sozeau, Gordon Stewart, David Swasey, Alexey Trilis, Quentin Vermande, Théo Zimmermann, wdewe, whonore
