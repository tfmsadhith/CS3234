Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

Fixpoint Sigma (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O =>
    f 0
  | S n' =>
    Sigma n' f + f n
  end.


Fixpoint Sigma_alt_aux (n : nat) (f : nat -> nat) (a : nat) : nat :=
  match n with
  | O =>
      a
  | S n' =>
      Sigma_alt_aux n' f (f n + a)
  end.

Definition Sigma_alt (n : nat) (f : nat -> nat) : nat :=
  Sigma_alt_aux n f (f 0).

Check (Nat.eqb).

Definition unit_test_for_Sigma (candidate : nat -> (nat -> nat) -> nat) : bool :=
  (candidate 5 (fun i => i) =? 15 ) &&
  (candidate 5 (fun i => i + 1) =? 21).


Compute (unit_test_for_Sigma Sigma).
Compute (unit_test_for_Sigma Sigma_alt).


Lemma fold_unfold_Sigma_O :
  forall (f : nat -> nat),
    Sigma 0 f =
    f 0.
Proof.
  fold_unfold_tactic Sigma.
Qed.

Lemma fold_unfold_Sigma_S :
  forall (n' : nat)
         (f : nat -> nat),
    Sigma (S n') f =
    Sigma n' f + f (S n').
Proof.
  fold_unfold_tactic Sigma.
Qed.



Lemma fold_unfold_Sigma_alt_aux_O :
  forall (f : nat -> nat)
         (a : nat),
    Sigma_alt_aux 0 f a = a.
Proof.
  fold_unfold_tactic Sigma_alt_aux.
Qed.

Lemma fold_unfold_Sigma_alt_aux_S :
  forall (n' : nat)
         (f : nat -> nat)
         (a : nat),
    Sigma_alt_aux (S n') f a = Sigma_alt_aux n' f (f (S n') + a).
Proof.
  fold_unfold_tactic Sigma_alt_aux.
Qed.

Lemma Sigma_alt_aux_reset:
  forall (n a : nat)
         (f : nat -> nat),
    Sigma_alt_aux n f a = a + Sigma_alt_aux n f 0.

Proof.
  intros n a f.
  revert a.

  induction n as [ | n' IHn'].

  * intros a.
    rewrite ->2 fold_unfold_Sigma_alt_aux_O.
    rewrite -> Nat.add_0_r.
    reflexivity.

  * intros a.
    rewrite ->1 fold_unfold_Sigma_alt_aux_S.
    rewrite -> (fold_unfold_Sigma_alt_aux_S  n').
    rewrite ->IHn'.
    rewrite -> (IHn' (f (S n') + 0)).
    rewrite -> (Nat.add_0_r).
    rewrite <- (Nat.add_shuffle3).
    rewrite -> (Nat.add_assoc).
    reflexivity.
Qed.
    
  
Theorem Sigma_and_Sigma_alt_are_equivalent_aux :
  forall (n : nat)
         (f : nat -> nat)
         (a : nat),
    Sigma n f + a = Sigma_alt_aux n f (f 0 + a).

Proof.
  intros n f.
  induction n as [ | n' IHn'].

  * intros a.
    rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_alt_aux_O.
    reflexivity.

  * intros a.
    rewrite -> Sigma_alt_aux_reset.
    rewrite -> fold_unfold_Sigma_alt_aux_S.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHn'.
    rewrite -> Sigma_alt_aux_reset.
    rewrite -> (Sigma_alt_aux_reset n' (f (S n') + 0)).
    rewrite -> Nat.add_0_r.
    rewrite -> Nat.add_shuffle1.
    rewrite -> (Nat.add_comm a).
    rewrite -> Nat.add_assoc.
    reflexivity.

  Restart.
  

  intros n f.
  
  induction n as [ | n' IHn'].
  intros a.
  
  - rewrite -> fold_unfold_Sigma_O.
    rewrite -> fold_unfold_Sigma_alt_aux_O.
    reflexivity.
  - intros a.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> fold_unfold_Sigma_alt_aux_S.
    rewrite -> Nat.add_assoc.
    rewrite -> (Nat.add_comm (f (S n')) (f 0)).
    rewrite <-  (Nat.add_assoc (f 0) (f (S n')) a).
    rewrite <- (Nat.add_assoc (Sigma n' f) (f (S n')) (a)).
    exact (IHn' (f (S n') + a)).
Qed.

Theorem Sigma_and_Sigma_alt_are_equivalent :
  forall (n : nat)
         (f : nat -> nat),
    Sigma n f = Sigma_alt n f.
Proof.
  intros n f.
  unfold Sigma_alt.
  rewrite <- (Nat.add_0_r (f 0)).
  rewrite <- (Nat.add_0_r (Sigma n f)).
  exact (Sigma_and_Sigma_alt_are_equivalent_aux n f 0).
Qed.




  
         
  







      
