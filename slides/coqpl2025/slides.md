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

---
layout: two-cols-header
title: HB
level: 2
---

# Hierarchy Builder

:: left ::

bla bla

* this 
* that 
* whatnot

:: right ::

```coq
From HB Require Import structures.
From Coq Require Import ssreflect ZArith.

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

# Track / [Trocq](https://github.com/coq-community/trocq)

A modular parametricity plugin for Coq. It can be used to achieve proof transfer by both translating a user goal into another variant.

:: left ::

bla

:: right ::

```coq
Definition RN : (N <=> nat)%P := Iso.toParamSym N.of_nat_iso.
Trocq Use RN. (* registering related types *)

(** This equivalence proof coerces to a relation of type `N -> nat -> Type`,
  which we show relates the respective zero and successor constants of these
  types: *)
Definition RN0 : RN 0%N 0%nat. Proof. done. Defined.
Definition RNS m n : RN m n -> RN (N.succ m) (S n). Proof. by case. Defined.
Trocq Use RN0 RNS. (* registering related constants *)

(** We can now make use of the tactic to prove an induction principle on `N` *)
Lemma N_Srec : forall (P : N -> Type), P 0%N ->
    (forall n, P n -> P (N.succ n)) -> forall n, P n.
Proof. trocq. (* replaces N by nat in the goal *) exact nat_rect. Defined.
```

---
layout: two-cols-header
level: 2
---

# Derive

:: left ::

:: right ::

---
layout: two-cols-header
level: 2
---

# Algebra Tactics

:: left ::
 
:: right ::



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
layout: image-right
image: logo.png
backgroundSize: 80%
level: 2
---

# Thanks! {style="text-align:center"}

![Homepage](/frame.png "qrcode"){style="width: 60%; margin-left:auto; margin-right: auto;"}

<span style="text-align:center">

https://github.com/LPCIC/coq-elpi/

</span>

<br/>

Questions? {style="text-align:center"}