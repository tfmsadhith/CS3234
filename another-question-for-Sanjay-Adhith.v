(* another-question-for-Sanjay-Adhith.v *)
(* CS3234, Sun 07 Apr 2024 *)

(* ********** *)

(* Paraphernalia: *)

Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith.

(* ********** *)

Definition specification_of_the_fibonacci_function (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib n'' + fib (S n'').

Definition test_fib (candidate: nat -> nat) : bool :=
  (candidate 0 =? 0)
  &&
  (candidate 1 =? 1)
  &&
  (candidate 2 =? 1)
  &&
  (candidate 3 =? 2)
  &&
  (candidate 4 =? 3)
  &&
  (candidate 5 =? 5)
  (* etc. *).

(* ********** *)

(* The two following implementations allegedly compute the Fibonacci function. *)

(* ***** *)

(* A recursive implementation: *)

Fixpoint r_fib_aux (n : nat) : nat * nat :=
  match n with
    O =>
    (0, 1)
  | S n' =>
    match r_fib_aux n' with
      (x, y) =>
      (y, x + y)
    end
  end.

Lemma fold_unfold_r_fib_aux_O :
  r_fib_aux 0 =
  (0, 1).
Proof.
  fold_unfold_tactic r_fib_aux.
Qed.

Lemma fold_unfold_r_fib_aux_S :
  forall n' : nat,
    r_fib_aux (S n') =
    match r_fib_aux n' with
      (x, y) =>
      (y, x + y)
    end.
Proof.
  fold_unfold_tactic r_fib_aux.
Qed.

Definition r_fib (n : nat) : nat :=
  match r_fib_aux n with
    (x, _) => x
  end.
Compute (test_fib r_fib).

(* ***** *)

(* A tail-recursive implementation: *)

Fixpoint tr_fib_aux (n : nat) (p : nat * nat) :=
  match n with
    O =>
    p
  | S n' =>
    match p with
      (x, y) =>
      tr_fib_aux n' (y, x + y)
    end
  end.

Lemma fold_unfold_tr_fib_aux_O :
  forall p : nat * nat,
    tr_fib_aux 0 p =
    p.
Proof.
  fold_unfold_tactic tr_fib_aux.
Qed.

Lemma fold_unfold_tr_fib_aux_S :
  forall (n' : nat)
         (p : nat * nat),
    tr_fib_aux (S n') p =
    match p with
      (x, y) =>
      tr_fib_aux n' (y, x + y)
    end.
Proof.
  fold_unfold_tactic tr_fib_aux.
Qed.

Definition tr_fib (n : nat) : nat :=
  match tr_fib_aux n (0, 1) with
    (x, _) => x
  end.

Compute (test_fib tr_fib).

(* ***** *)

(* a. Prove whether these two implementations indeed compute the Fibonacci function
      (and if you get stuck, forge ahead to Question b.): *)


(* A standard naive fibonacci *)

Fixpoint fib (n : nat) : nat :=
  match n with
  | O =>
    0
  | S n' => match n' with
            | O =>
              1
            | S n'' =>     
              fib n' + fib n''
            end            
  end.

Compute (fib 0, fib 1, fib 2, fib 3, fib 4, fib 5, fib 6, fib 7, fib 8).

Lemma fold_unfold_fib_O :
  fib O = O.

Proof.
  fold_unfold_tactic fib.
Qed.  

Lemma fold_unfold_fib_S :
  forall n' : nat,
     fib (S n') =
     match n' with
     | 0 =>
       1
     | S n'' =>
       fib n' + fib n''
    end.

Proof.
  fold_unfold_tactic fib.
Qed.

Definition fib_satisfies_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function fib.

Proof.
  unfold specification_of_the_fibonacci_function.
  split.

  * rewrite -> fold_unfold_fib_O.
    reflexivity.

  * split.

    - rewrite -> fold_unfold_fib_S.
      reflexivity.

    - intros n.
      rewrite -> fold_unfold_fib_S.
      rewrite -> Nat.add_comm.
      reflexivity.
Qed.
      
(* Conjecture that the head
   contains the fib n while the
   tail contains fib S n *)

Check r_fib_aux.
Compute (r_fib_aux 0, r_fib_aux 1, r_fib_aux 2, r_fib_aux 3, r_fib_aux 4, r_fib_aux 5, r_fib_aux 6, r_fib_aux 7).

(* Seems to hold *)


Lemma about_r_fib_aux :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall n : nat,
      r_fib_aux n = (fib n, fib (S n)).

Proof.
  intros fib [S_fib_O [S_fib_1 S_fib_S]] n.
  induction n as [ | n' IHn'].

  * rewrite -> S_fib_O.
    rewrite -> S_fib_1.
    rewrite -> fold_unfold_r_fib_aux_O.
    reflexivity.

  * rewrite -> S_fib_S.
    rewrite -> fold_unfold_r_fib_aux_S.
    rewrite -> IHn'.
    reflexivity.
Qed.    

Proposition r_fib_satisfies_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function r_fib.
Proof.
  unfold specification_of_the_fibonacci_function.
  unfold r_fib.

  split.

  * rewrite -> fold_unfold_r_fib_aux_O.
    reflexivity.

  * split.

    - rewrite -> fold_unfold_r_fib_aux_S.
      rewrite -> fold_unfold_r_fib_aux_O.
      reflexivity.

    - intros n.
      rewrite ->2 fold_unfold_r_fib_aux_S.
      rewrite -> (about_r_fib_aux fib fib_satisfies_specification_of_the_fibonacci_function n).
      reflexivity.
Qed.
      
      
Compute r_fib_aux 0.
Check tr_fib_aux.

(* Learning from our lesson with
   factorials, we will learn to use
   valid initial states of the
   accumulator *)

Compute (tr_fib_aux 1 (1,1)).
Compute (tr_fib_aux 2 (1,2)).
Compute (tr_fib_aux 4 (0,1)).

Lemma about_tr_fib_aux :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall n m: nat,
      tr_fib_aux n (fib m , fib (S m)) = (fib (n + m),
                                          fib (S m + n)).

Compute (tr_fib_aux 10 (0,1)).

Proof.
  intros fib [fib_O [fib_1 fib_S]].

  intros n.
  induction n as [ | n' IHn'].

  * intros m.
    rewrite -> fold_unfold_tr_fib_aux_O.
    rewrite -> Nat.add_0_l.
    rewrite -> Nat.add_0_r.
    reflexivity.

  * intros m.
    rewrite -> fold_unfold_tr_fib_aux_S.
    rewrite <- fib_S.
    (* The asserts just factor out
       associative-commutative rewriting
       from the proof *)
    assert (H : S n' + m  = n' + S m).
    {
      ring.
    }
    rewrite -> H.
    assert (J : S m + S n' = S (S (m)) + n').
    {
      ring.
    }
    rewrite -> J.
    rewrite <- IHn'.
    reflexivity.
Qed.    

    
Proposition tr_fib_satisfies_the_specification_of_the_fibonacci_function :
  specification_of_the_fibonacci_function tr_fib.

Proof.
  unfold specification_of_the_fibonacci_function, tr_fib.
  split.

  * rewrite -> fold_unfold_tr_fib_aux_O.
    reflexivity.

  * split.

    - rewrite -> fold_unfold_tr_fib_aux_S.
      rewrite -> fold_unfold_tr_fib_aux_O.
      reflexivity.

    - intros n.
      Check fold_unfold_tr_fib_aux_O.
      rewrite <- (fold_unfold_fib_O) at 1 3 5.
      Search (_ = S _).
      assert (H : fib (S(0) + 0) = 1).
      {
        rewrite -> fold_unfold_fib_S.
        reflexivity.
      }
      rewrite <- H.
      rewrite <- (Nat.add_0_l 0) at 1 3 5.
      rewrite ->3 (about_tr_fib_aux fib fib_satisfies_specification_of_the_fibonacci_function).
      rewrite -> Nat.add_0_l.
      rewrite ->3 Nat.add_0_r.
      rewrite -> fold_unfold_fib_S.
      rewrite -> Nat.add_comm.
      reflexivity.
Qed.      

(* ***** *)

Fixpoint nat_fold_right (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
    O =>
    zero_case
  | S n' =>
    succ_case (nat_fold_right V zero_case succ_case n')
  end.

Lemma fold_unfold_nat_fold_right_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_right V zero_case succ_case O =
    zero_case.
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Lemma fold_unfold_nat_fold_right_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_right V zero_case succ_case (S n') =
      succ_case (nat_fold_right V zero_case succ_case n').
Proof.
  fold_unfold_tactic nat_fold_right.
Qed.

Fixpoint nat_fold_left (V : Type) (zero_case : V) (succ_case : V -> V) (n : nat) : V :=
  match n with
    O =>
      zero_case
  | S n' =>
      nat_fold_left V (succ_case zero_case) succ_case n'
  end.

Lemma fold_unfold_nat_fold_left_O :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V),
    nat_fold_left V zero_case succ_case O =
      zero_case.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

Lemma fold_unfold_nat_fold_left_S :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_left V zero_case succ_case (S n') =
      nat_fold_left V (succ_case zero_case) succ_case n'.
Proof.
  fold_unfold_tactic nat_fold_left.
Qed.

(* ***** *)

(* b. Since r_fib_aux is recursive,
      implement it as an instance of nat_fold_right,
      and prove that the two implementations are equivalent.
 *)

Compute nat_fold_right (nat * nat)
  (0,1)
  (fun ih =>
     match ih with
       (x, y) =>
         (y, x + y)
     end) 2.


Definition r_fib_aux_right (n : nat) : nat * nat :=
  nat_fold_right (nat * nat)
    (0, 1)
    (fun ih =>
       match ih with
         (x, y) =>
           (y, x + y)
       end)
    n.

Proposition r_fib_aux_and_r_fib_aux_right_are_equivalent :
  forall n : nat,
    r_fib_aux n = r_fib_aux_right n.

Proof.
  unfold r_fib_aux, r_fib_aux_right.
  intros n.
  induction n as [ | n' IHn'].

  * rewrite -> fold_unfold_nat_fold_right_O.
    reflexivity.

  * rewrite -> fold_unfold_nat_fold_right_S.
    rewrite -> IHn'.
    reflexivity.
Qed.

(* ***** *)

(* c. Since tr_fib_aux is tail-recursive and uses an accumulator,
      implement it as an instance of nat_fold_left,
      and prove that the two implementations are equivalent.
 *)

Check nat_fold_left.
Check nat_fold_right.
Definition tr_fib_aux_left (n : nat) (p : nat * nat) : nat * nat :=
  nat_fold_left  (nat * nat)
    p
    (fun a =>
       match a with
         (x, y) =>
           (y, x + y)
       end)
    n.

Compute tr_fib_aux_left 0.
Compute tr_fib_aux 0.

(* Typo: r_fib_aux_left -> tr_fib_aux_left *)
(* I am only considering valid states of the
   accumulator *)
Proposition tr_fib_aux_and_tr_fib_aux_left_are_equivalent :
  forall fib : nat -> nat,
    specification_of_the_fibonacci_function fib ->
    forall n t: nat,
      tr_fib_aux n (fib t, fib (S t))
      = tr_fib_aux_left n (fib t, fib (S t)).

Proof.
  unfold tr_fib_aux_left.
  intros fib [S_fib_O [S_fib_1 S_fib_S]] n.
  induction n as [ | n' IHn'].
  
  * intros t.
    rewrite -> fold_unfold_tr_fib_aux_O.
    rewrite -> fold_unfold_nat_fold_left_O.
    reflexivity.

  * intros t.
    rewrite -> fold_unfold_tr_fib_aux_S.
    rewrite -> fold_unfold_nat_fold_left_S.
    rewrite <- S_fib_S.
    rewrite <- IHn'.
    reflexivity.
Qed.    

(* ***** *)

Definition r_fib_right (n : nat) : nat :=
  match r_fib_aux_right n with
    (x, _) => x
  end.

Compute (test_fib r_fib_right).

Definition tr_fib_left (n : nat) : nat :=
  match tr_fib_aux_left n (0,1) with
    (x, _) => x
  end.

Compute (test_fib tr_fib_left).
Compute (test_fib r_fib_right).

(* d. Prove that r_fib_right and tr_fib_left are equivalent
      as a corollary of Theorem folding_left_and_right_over_nats
      (named nat_fold_right_is_equivalent_to_nat_fold_left in your midterm project)
 *)


Lemma nat_fold_left_resets:
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n' : nat),
    nat_fold_left V zero_case succ_case (S n') = succ_case (nat_fold_left V zero_case succ_case n').
Proof.
  intros V zero_case succ_case n'.
  revert zero_case.
  induction n' as [ | n'' IHn''].

  * intro zero_case.
    rewrite -> (fold_unfold_nat_fold_left_S V zero_case succ_case 0).
    rewrite -> (fold_unfold_nat_fold_left_O V zero_case succ_case).
    exact (fold_unfold_nat_fold_left_O V (succ_case zero_case) succ_case).

  * intro zero_case.
    rewrite -> (fold_unfold_nat_fold_left_S V zero_case succ_case (S n'')).
    rewrite -> (fold_unfold_nat_fold_left_S V zero_case succ_case n'').
    exact (IHn'' (succ_case zero_case)).
Qed.


Proposition nat_fold_right_is_equivalent_to_nat_fold_left :
  forall (V : Type)
         (zero_case : V)
         (succ_case : V -> V)
         (n : nat),
    nat_fold_right V zero_case succ_case n = nat_fold_left V zero_case succ_case n.
Proof.
  intros V zero_case succ_case.
  induction n as [ | n' IHn'].

  * rewrite -> (fold_unfold_nat_fold_left_O V zero_case succ_case).
    exact (fold_unfold_nat_fold_right_O V zero_case succ_case).

  * rewrite -> (nat_fold_left_resets V zero_case succ_case n').
    rewrite -> (fold_unfold_nat_fold_right_S V zero_case succ_case n').
    rewrite -> IHn'.
    reflexivity.
Qed.

Corollary r_fib_right_and_tr_fib_left_are_equivalent:
  forall n : nat,
    r_fib_right n = tr_fib_left n.

Proof.
  unfold r_fib_right, tr_fib_left, r_fib_aux_right, tr_fib_aux_left.
  intros n.

  rewrite -> (nat_fold_right_is_equivalent_to_nat_fold_left
                (nat * nat)
                (0, 1)
                (fun a =>
                   match a with
                     (x, y) =>
                       (y, x + y)
                   end)
                n).

  reflexivity.
Qed.  
  
(* ********** *)

(* end of another-question-for-Sanjay-Adhith.v *)
