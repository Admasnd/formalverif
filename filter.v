Require Import List.

Fixpoint filter {X : Type} (p : X -> bool) (l: list X) : list X :=
  match l with
    | nil => nil
    | x :: xs => if p x then x :: (filter p xs) else filter p xs
  end.

Theorem filter_correct : forall (X : Type) (p : X -> bool)
                          (l l' : list X) (x : X),
                           In x l -> l' = filter p l -> p x = true -> In x l'.
Proof.
  intros X p l.
  induction l as [| y ys].
  intros l' x H1 H2 H3.
  inversion H1.
  intros l' x H1 H2 H3.
  simpl in H2.
  simpl in H1.
  destruct H1.
  rewrite <- H in H3.
  destruct (p y) eqn:H4.
  rewrite -> H2.
  rewrite <- H.
  constructor.
  reflexivity.
  inversion H3.
  destruct (p y) eqn:H4.
  specialize (IHys (filter p ys) x H).
  rewrite -> H2.
  eapply in_cons.
  apply IHys.
  reflexivity.  
  assumption.
  rewrite -> H2.
  specialize (IHys (filter p ys) x H).
  apply IHys.
  reflexivity.
  assumption.
Qed.
