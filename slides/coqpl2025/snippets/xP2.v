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

Elpi Db tb.db lp:{{
pred tb i:term, o:term.

:name "tb:fail"
tb Ty _ :- coq.error "Cannot solve" {coq.term->string Ty}.

}}.

Elpi Tactic to_bool.
Elpi Accumulate Db tb.db.
Elpi Accumulate lp:{{

% tb {{ is_even lp:N }} {{ evenP lp:N }} :- !.
% tb {{ lp:P /\ lp:Q }} {{ andPP lp:PP lp:QQ }} :- tb P PP, tb Q QQ, !.

solve (goal Ctx _ Ty _ _ as G) GL :-
  tb Ty P,
  coq.say P,
  refine {{ elimT lp:P _ }} G GL.

}}.

Elpi Command add_tb.
Elpi Accumulate Db tb.db.
Elpi Accumulate lp:{{

pred compile i:term, i:term, i:list prop, o:prop.
compile {{ reflect lp:Ty _ }} P Hyps (tb Ty P :- Hyps).
compile {{ reflect lp:S _ -> lp:T }} P Hyps (pi h\ C h) :-
  pi h\
    compile T {{ lp:P lp:h }} [tb S h|Hyps] (C h).
compile {{ forall x, lp:(T x) }} P Hyps (pi h\ C h) :-
  pi x\
    compile (T x) {{ lp:P lp:x }} Hyps (C x).
    
main [str S] :-
  coq.locate S GR,
  coq.env.typeof GR Ty,
  compile Ty (global GR) [] C,
  coq.elpi.accumulate _ "tb.db" (clause _ (before "tb:fail") C).

}}.

Elpi add_tb evenP.
Elpi add_tb andPP.
Print LoadPath.

Elpi Print to_bool "Demo.snippets/to_bool".


Lemma test : is_even 6 /\ is_even 4.
elpi to_bool.
simpl.

