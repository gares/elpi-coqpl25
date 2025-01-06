From Coq Require Import Bool ssreflect ssrbool Arith.
From elpi Require Import elpi.

Set Printing Coercions.
Print iff.
About proj1.
About proj2.
Print reflect.
Search reflect andb.
About elimT.

Definition andPP  {P Q : Prop} {p q : bool} :
  reflect P p -> reflect Q q -> reflect (P /\ Q) (p && q) := andPP.

Inductive is_even : nat -> Prop :=
  | E0 : is_even 0
  | Eo n : is_odd n -> is_even (1+n)
with is_odd : nat -> Prop :=
  | Oe n : is_even n -> is_odd (1+n).

Hint Resolve E0.

Fixpoint even n : bool :=
  match n with
  | O => true
  | S (S n) => even n
  | _ => false
  end.

Lemma evenP n : reflect (is_even n) (even n).
Admitted.

Elpi Tactic to_bool.
Elpi Accumulate lp:{{

pred tb i:term, o:term.
tb {{ is_even lp:N }} {{ evenP lp:N }} :- !.
tb {{ lp:P /\ lp:Q }} {{ andPP lp:PP lp:QQ }} :- tb P PP, tb Q QQ, !.
tb Ty _ :- coq.error "Cannot solve" {coq.term->string Ty}.

solve (goal Ctx _ Ty _ _ as G) GL :-
  tb Ty P,
  coq.say P,
  refine {{ elimT lp:P _ }} G GL.

}}.

Lemma test : is_even 6 /\ is_even 4.
elpi to_bool.
simpl.

