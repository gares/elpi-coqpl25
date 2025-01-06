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
layout: two-cols-header
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
---

# Derive

:: left ::

:: right ::

---
layout: two-cols-header
---

# Algebra Tactics

:: left ::
 
:: right ::



---
layout: section
color: rocq
---

# Elpi in a nutshell


---
layout: two-cols-header
---

# Elpi: Hello World!

::left::

Simply typed $\lambda$-calculus in HOAS

<<< @/snippets/stlc.elpi#types elpi

Typing

<<< @/snippets/stlc.elpi#of elpi

::right::

```
goal> of (lam x\ lam y\ x) TyFst.

Success:
  TyFst = arr X0 (arr X1 X0)
```

```
goal> of (app H A) T.

Failure.
```



---
layout: two-cols-header
---

# Elpi: $\lambda$Prolog + CHR

::left::

Typing (as before)

<<< @/snippets/stlc.elpi#of elpi

Holes & constraints

<<< @/snippets/stlc.elpi#cst elpi

<v-click at="4">
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
---

# Integration in Rocq

---
layout: section
color: rocq
---

# The good company

---
transition: fade

---

# Comparison

| | ==Elpi== | Ltac2 | MetaCoq |
|--|--|--|--|
| Gallina | | |
| Bound Variables | <icon-park-twotone-pie-five/><sup>1</sup> | <icon-park-twotone-round/> |
| Holes (evars) | <meteocons-thunderstorms-extreme-fill/> | <carbon-rain/> |
| Quotations | <carbon-thunderstorm/> | <carbon-sun/> |
| Vernacular API | |
| Tactic API | <Thumb width="1em"/> |


<div style="position:absolute; bottom: 0; font-size: medium" class="flex justify-center gap-3">

<div>1) missing mutual ind/fix</div>

<div>2) bli</div>

</div>


---
layout: center
---

# Thanks!