(* The following proof of Strong Induction obtained here:
   http://pldev.blogspot.com/2012/02/proving-strong-induction-principle-for.html

   Code comes from above blog post.
*)

Section InductionPrinciple.


Require Export Datatypes.

Variable P : nat -> Prop.

Lemma le_S :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right. reflexivity.
  left. assumption.
Qed.

Theorem strongind_aux :
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert (m <= n' \/ m = S n'). apply le_S. assumption.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'); assumption.
Qed.

Lemma weaken :
  (forall n, (forall m, ((m <= n) -> P m))) -> (forall n, P n).
Proof.
  intros H n.
  apply (H n n).
  apply le_n.
Qed.

Theorem strongind :
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.

End InductionPrinciple.

