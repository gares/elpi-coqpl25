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

<div class="flex justify-center items-center">

<div>

![Elpi logo](/logo.png "Logo")

</div>

</div>


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
layout: center
---

# Thanks!