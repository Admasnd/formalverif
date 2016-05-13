Require Import Coq.Lists.List.
Require Import Omega. (* Needed to use omega tactic to do automated proofs of goals involving inequalities of numbers. *)
Require Import Sorting.Permutation.
Require Import StrongInduction.

(* Included because the Notations defined in List library not showing up *)
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..). 

(* Split Spec *)
Module Type Split_SPEC .
  Parameter split : forall (X : Type), list X -> list X * list X.                 
  Arguments split [X] _.

  Axiom split_nil : forall (X : Type), split (@nil X) = (@nil X,@nil X).
  Axiom split_sing : forall (X : Type) (x : X), split [x] = ([x],@nil X).
  Axiom split_mult : forall (X : Type) (x y : X) (ys : list X), 
                     exists (l1 l2 : list X), split (x :: y :: ys) = (x :: l1, y :: l2) /\ split ys = (l1,l2).
End Split_SPEC.

(* Verify Split Spec *)
Module Split_Correct (S : Split_SPEC).

  (* Induction on length of list *)
  Lemma split_length_aux : forall (n : nat), (fun n =>
                             forall (X : Type) (l l1 l2 : list X),
                             n = length l -> S.split l = (l1,l2) -> 
                             length l = length l1 + length l2) n.
  Proof.
   (* Using strong induction *)
   apply strongind;
   intros;
   try match goal with
       H : context[S.split ?l] |- _ => destruct l (* Proof by Cases *)
   end;
   try match goal with
       | H : context[S.split (_ :: ?l)] |- _ => destruct l (* Proof by Cases *)
   end;  
   repeat match goal with
       | H : context[S.split nil] |- _ => rewrite S.split_nil in H; inversion H (* Get two empty lists as equations *)
       | H1 : ?l = nil, H2: S.split ?l = (_,_) |- _ =>
         rewrite H1 in H2; rewrite S.split_nil in H2; inversion H2 (* Variant of previous match *)
       | H : context[S.split [?x]] |- _ => rewrite S.split_sing in H; inversion H
       | H : context[0 = length _] |- _ => symmetry in H; rewrite length_zero_iff_nil in H (* infer nil *)
       | H : context[(_ :: _) = nil] |- _ => inversion H (* contradiction in hypotheses *)
       | H : ?l = nil |- context[?l] => rewrite H (* rewrite goal with nil *)
   end;
   try match goal with
       | H1 : context[S.split (?x :: ?y :: ?ys)], H2 : ?X : Type |- _ => let H3 := fresh in
           assert (exists (l1 l2 : list X), S.split (x::y::ys) = (x::l1,y::l2) /\
           S.split l = (l1,l2)) as H3 by apply S.split_mult; do 3 destruct H3 (* existential and AND elimination *)
   end;   
   try match goal with
         | H1 : S.split (?x::?y::?ys) = (?l1,?l2),
           H2 : S.split (?x::?y::?ys) = (?x::_,?y::_) |- _ =>
           rewrite -> H2 in H1; inversion H1 (* show two hypotheses are equal *)
   end;                                             
   try match goal with
         | H : S ?n = length (_ :: _ :: ?xs) |- _ => let H1 := fresh in
                                                     let H2 := fresh in 
            assert (length xs < S n) as H1 by (rewrite H; simpl; omega);
            assert (length xs <= n) as H2 by omega  (* get precondition for strong induction hypothesis *)
   end;
   (* Inductive Proof *)
   try match goal with
         | H1 : S.split ?ys = (?l1,?l2), H2 : length ?ys <= ?n, X : Type,
           H3 : S.split (?x::?y::?ys) = (?x::?l1,?y::?l2), H4: context[forall _, _]
           |- length (?x::?y::?ys) = length (?x::?l1) + length (?y::?l2) =>
           let H5 := fresh in
           assert (length l = length l) as H5 by reflexivity;
           specialize (H4 (length l) H2 X l l1 l2 H5); (* universal elimination *)
           apply H4 in H1; simpl;
           rewrite <- plus_n_Sm;
           rewrite <- H1
   end;
   auto.
  Qed.

  (* Correctnesss property *)
  Theorem split_length : forall (X : Type) (l l1 l2 : list X), S.split l = (l1,l2)
                            -> length l = length l1 + length l2.
  Proof.
    intros.
    eapply split_length_aux.
    exists.
    assumption.
  Qed.  
End Split_Correct.

Module Split_IMPL : Split_SPEC.

 Fixpoint split {X : Type} (l: list X) : list X * list X :=
    match l with
      | nil => (nil,nil)
      | x :: nil => (x :: nil,nil)
      | x :: y :: xs => let (l1, l2) := split xs in
                            (x :: l1, y :: l2)
    end.

  Theorem split_nil : forall (X : Type), split (@nil X) = (@nil X,@nil X).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem split_sing : forall (X : Type) (x : X), split [x] = ([x],@nil X).
  Proof.
    intros.
    reflexivity.
  Qed.
    
  Theorem split_mult : forall (X : Type) (x y : X) (ys : list X), 
                       exists (l1 l2 : list X),
                       split (x :: y :: ys) = (x :: l1, y :: l2) /\ split ys = (l1,l2).
  Proof.
    intros.
    destruct (split (x :: y :: ys)) eqn:H1.
    simpl in H1.
    destruct (split ys) eqn:H2.
    exists l1. 
    exists l2.
    split.
    rewrite H1.
    reflexivity.
    reflexivity.
  Qed.

End Split_IMPL.


Module Split_Bram : Split_SPEC.

 Fixpoint split {X : Type} (l: list X) : list X * list X :=
    match l with
      | nil => (nil,nil)
      | x :: xs => let (l1, l2) := split xs in
                            (x :: l2, l1)
    end.

  Theorem split_nil : forall (X : Type), split (@nil X) = (@nil X,@nil X).
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem split_sing : forall (X : Type) (x : X), split [x] = ([x],@nil X).
  Proof.
    intros.
    reflexivity.
  Qed.
    
  (* Do not even need to change proof in Prof. Bram's implementation *)
  Theorem split_mult : forall (X : Type) (x y : X) (ys : list X), 
                       exists (l1 l2 : list X),
                       split (x :: y :: ys) = (x :: l1, y :: l2) /\ split ys = (l1,l2).
  Proof.
    intros.
    destruct (split (x :: y :: ys)) eqn:H1.
    simpl in H1.
    destruct (split ys) eqn:H2.
    exists l1. 
    exists l2.
    split.
    rewrite H1.
    reflexivity.
    (*reflexivity.i*)
  Qed.

End Split_Bram.


