From Coq Require Import Bool ssreflect ssrbool.
From elpi Require Import elpi.

Axiom is_even : nat -> Prop.

Fixpoint even n : bool :=
  match n with
  | O => true
  | S (S n) => even n
  | _ => false
  end.

Lemma evenP n : reflect (is_even n) (even n).
Admitted.

Lemma andP  {P Q : Prop} {p q : bool} :
  reflect P p -> reflect Q q ->
    reflect (P /\ Q) (p && q).
Admitted.

Lemma elimT {P b} :
  reflect P b -> b = true ->
    P.
Admitted.

Lemma test : is_even 6 /\ is_even 4.
Proof.
  refine (elimT (andP (evenP 6) (evenP 4)) _).
  (* elpi to_bool. *)
  simpl.
  trivial.
Qed.
