Require Import List.
Require Import EquivDec.
Module Type Remove_Correctness.

   Parameter remove : forall (X : Type) {eq : EqDec X eq} , list X -> X -> list X.

   Arguments remove [X] _ _ _ .

   Axiom remove_exclusion : forall (X : Type) {eq : EqDec X eq} (x : X) (l : list X), ~ In x (remove eq l x).

   Axiom remove_subset : forall (X : Type) {eq : EqDec X eq} (x : X) (y : X) (l : list X), x =/= y -> In x l <-> In x (remove eq l y).
End Remove_Correctness.

Module Type Remove_Spec.

  Parameter remove : forall (X : Type) {eq : EqDec X eq}, list X -> X -> list X.

  Arguments remove [X] _ _ _.

  Axiom remove_nil : forall (X : Type) {eq : EqDec X eq} (x : X), remove eq nil x = nil.

  Axiom remove_exclude : forall (X : Type) {eq : EqDec X eq} (x : X) (xs : list X), remove eq (x :: xs) x = remove eq xs x.

  Axiom remove_keep : forall (X : Type) {eq : EqDec X eq} (x y : X) (xs : list X), x =/= y -> remove eq (x :: xs) y = x :: (remove eq xs y).

End Remove_Spec.

Module Remove_Correct (P : Remove_Spec) : Remove_Correctness.

  Theorem remove_exclusion : forall (X : Type) {eq : EqDec X eq} (x : X) (l : list X), ~ In x (P.remove eq l x).
    intros.
    unfold not. (* ~ aka not defined as P -> False *)
    intros.
    (* Proof goal is to show that x being in the result of remove leads to contradiction *)
    induction l as [| y ys].
    (* Base Case *)
    rewrite P.remove_nil in H.
    simpl in H.
    assumption.
    (* Inductive Case *)
    destruct (eq x y) eqn:H1.
    (* x == y *)
    rewrite <- e in H.
    rewrite P.remove_exclude in H.
    apply IHys in H.
    assumption.
    (* x =/= y *)
    apply IHys.
    assert (P.remove eq (y :: ys) x = y :: (P.remove eq ys x)) as H2.
    apply P.remove_keep.
    assert (y =/= x) as H3.
    symmetry.
    assumption.
    assumption.
    rewrite H2 in H.
    simpl in H.
    destruct H.
    (* Case y = x *)
    assert (x === y) as H4.
    rewrite H.
    reflexivity.
    contradiction.
    (* Case In x (P.remove eq ys x) *)
    assumption.
  Qed.
    
   Theorem remove_subset : forall (X : Type) {eq : EqDec X eq} (x : X) (y : X) (l : list X), x =/= y -> In x l <-> In x (P.remove eq l y).
     intros.
     split.
     (* -> *)
     intros.
     induction l as [| z zs].
     (* Base Case *)
     rewrite P.remove_nil.
     assumption.
     (* Inductive Case *)
     destruct (eq y z) eqn:H1.
     (* y == z *)
     assert (P.remove eq (z :: zs) y = P.remove eq zs y) as H2.
     rewrite e.
     apply P.remove_exclude.
     rewrite H2.
     apply IHzs.
     destruct H0.
     (* z = x *)
     assert (x === y) as H3.
     assert (z === y) as H4.
     symmetry.
     assumption.
     rewrite -> H0 in H4. 
     assumption.
     contradiction.
     (* In x zs *)
     assumption.
     (* y =/= z *)
     assert (P.remove eq (z :: zs) y = z :: (P.remove eq zs y)) as H2.
     apply P.remove_keep.
     symmetry.
     assumption.
     rewrite H2.
     simpl.
     simpl in H0.
     destruct H0.
     left.
     assumption.
     right.
     apply IHzs.
     assumption.
     (* <- *)
     intros.     
     induction l as [| z zs].
     rewrite P.remove_nil in H0.
     assumption.
     simpl.
     destruct (eq y z) eqn:H1.
     right.
     apply IHzs.
     assert (P.remove eq (z :: zs) y = P.remove eq zs y) as H2.
     rewrite e.
     apply P.remove_exclude.
     rewrite H2 in H0.
     assumption.
     assert (P.remove eq (z :: zs) y = z :: (P.remove eq zs y)) as H2.
     apply P.remove_keep.
     symmetry.
     assumption.
     rewrite H2 in H0.
     simpl in H0.
     destruct H0.
     left.
     assumption.
     right.
     apply IHzs.
     assumption.
   Qed.

   Definition remove := P.remove.

End Remove_Correct.

 
Module Remove_IMPL : Remove_Spec.

  Fixpoint remove {X : Type } {eq : EqDec X eq} (l : list X) (x : X) : list X :=
    match l with
      | nil => nil
      | y :: ys => if eq x y then remove ys x else y :: (remove ys x)
    end.

  Theorem remove_nil : forall (X : Type) {eq : EqDec X eq} (x : X), remove nil x = nil.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem remove_exclude : forall (X : Type) {eq : EqDec X eq} (x : X) (xs : list X), remove (x :: xs) x = remove xs x.
  Proof.
    intros.
    simpl.
    destruct (eq x x) eqn:H1.
    reflexivity.
    assert (x === x) as H2.
    reflexivity.
    contradiction.
   Qed.

  Theorem remove_keep : forall (X : Type) {eq : EqDec X eq} (x y : X) (xs : list X), x =/= y -> remove (x :: xs) y = x :: (remove xs y).
  Proof.
    intros.
    simpl.
    destruct (eq y x) eqn:H1.
    symmetry in H.
    contradiction.
    reflexivity.
  Qed.
End Remove_IMPL.
   



   