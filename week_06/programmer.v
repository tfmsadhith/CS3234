Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.

Require Import Arith Nat Bool.

(*

Introduction
------------

This is the programmers approach, the kernel
of this approach involves writing a program
that checks if a number is even, and proving
properties about that program to prove theorems.

The main tool used to prove properties about
the program is induction.

Sketch of proof of n*(Sn) is even for all n.
--------------------------------------------

Let P(n) be the proposition that n*(Sn)
is even.

Base case
---------

0*1 = 0. 0 is even.

Inductive step
--------------

is_even (n*(Sn)) = true -> is_even (Sn) * (S(Sn))) = true
                   
 (Sn) * (S (S n))
= (Sn) * (2 + n)
= (Sn)*2 + (Sn)*n

To show that this expression, we need
to prepare to lemmas, one to show that
twice any natural number is even and
another to show that an even number plus
an even number give an even number. 

*)


Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 =>
    true
  | S n' =>
    eqb (is_even n') false
  end.

Lemma fold_unfold_is_even_0:
  is_even 0 = true.

Proof.
  fold_unfold_tactic is_even.
Qed.

Lemma fold_unfold_is_even_S:
  forall n' : nat,
    is_even (S n') = eqb (is_even n') false.

Proof.
  fold_unfold_tactic is_even.
Qed.


(*

  I am taking care not to confuse
  not even with odd.

  To show that if a number is not
  even, then it is odd requires a
  proof.

  We will sidestep this issue for
  now by not considering odd numbers,
  which we don't need for this
  exercise.

*)


Lemma successor_flips_evenness:
  forall n : nat,
    is_even n = negb (is_even (S n)).

Proof.
  intro n.
  rewrite -> (fold_unfold_is_even_S n).
  destruct (is_even n).

  * simpl.
    reflexivity.

  * simpl.
    reflexivity.
Qed.

Lemma predecessor_flips_evenness:
  forall n : nat,
    is_even (S n) = negb (is_even n).

Proof.
  intro n.
  rewrite -> (fold_unfold_is_even_S n).
  destruct (is_even n).

  * simpl.
    reflexivity.
  * simpl.
    reflexivity.
Qed.

Lemma predecessor_of_even_is_not_even:
  forall n : nat,
    (is_even (S n) = true) ->
      (is_even n = false).

Proof.
  intro n.
  rewrite -> fold_unfold_is_even_S.
  destruct (is_even n).

  * simpl.
    discriminate.

  * simpl.
    intro H.
    reflexivity.
Qed.

Lemma predecessor_of_not_even_is_even:
  forall n : nat,
    (is_even (S n) = false) ->
      (is_even n = true).

Proof.
  intro n.
  rewrite -> fold_unfold_is_even_S.
  destruct (is_even n).

  * simpl.
    intro H.
    reflexivity.

  * simpl.
    discriminate.
Qed.


Lemma two_times_natural_is_even:
  forall k : nat,
    is_even (2 * k) = true.

Proof.
  intro k.
  induction k as [ | k' IHk'].

  * rewrite -> (Nat.mul_0_r 2).
    exact fold_unfold_is_even_0.

  * rewrite <- (Nat.add_1_l k').
    Search (_ * (_ + _)).
    rewrite -> (Nat.mul_add_distr_l 2 1 k').
    rewrite -> (Nat.mul_1_r 2).
    rewrite <- (Nat.add_1_l 1) at 1.
    rewrite <- (Nat.add_assoc 1 1 (2 * k')).
    rewrite -> (Nat.add_1_l (1 + 2 * k')).
    rewrite -> (Nat.add_1_l (2 * k')).
    rewrite -> (fold_unfold_is_even_S (S (2 * k'))).
    rewrite -> (fold_unfold_is_even_S (2 * k')).
    rewrite -> IHk'.
    simpl.
    reflexivity.
Qed.


Lemma even_is_two_times_natural:
  forall n : nat,
    (is_even n = true) ->
     exists k : nat, 
         2*k = n.

(*
  Trying to prove this lemma by induction
  on n immediately is not feasible. Here is
  why:

  let P(n) be the proposition that for all
  n (is_even n = true -> exists k : nat, 2*k = n).

  Using the hypothesis to show
  (is_even (S n) = true -> exists k : nat, 2*k = S n).
  is impossible because to get to the existential
  quantifier you need is_even n = true.


  Of course, with is_even (S n) = true in our
  assumptions, we can never get to is_even n = true,
  because is_even n = false.

                   *** 

  So we prove a more general version of the lemma
  that also consider the case when is_even n = false.

  Then if we have is_even (S n) = true, we can use
  is_even n = false to get to an existential
  quantifier.

  Since we are proving a more general version of the
  lemma, we also need to consider is_even (S n) = false,
  and we can use is_even n = true to get to the needed
  existential quantifier here.

*)

Proof.
  intro n.
  assert (both : (is_even n = true -> exists k : nat, 2 * k = n)
              /\
              (is_even n = false -> exists k : nat, S(2 * k) = n)).

  induction n as [ | n' IHn'].

  * split.
    -  intro H_0.
       exists 0.
       rewrite -> (Nat.mul_0_r 2).
       reflexivity.
    -  rewrite -> fold_unfold_is_even_0.
       discriminate.

  * destruct IHn' as [H_even H_not_even].
    split.
    
    - intro H_S_n.
      rewrite <- (Nat.add_1_r n').
      assert (H_n : is_even n' = false).

      + exact (predecessor_of_even_is_not_even n' H_S_n).

      + Check (H_not_even).

        assert (H : (exists k : nat, S (2 * k) = n') -> (exists t : nat, 2 * t = n' + 1)).

        ** intro H_k.
           destruct H_k as [k H_S_k].
           exists (k + 1).
           rewrite <- H_S_k.

           rewrite <- (Nat.add_1_r (2 * k)).
           Search (_*(_ + _)).
           rewrite -> (Nat.mul_add_distr_l 2 k  1).
           rewrite -> (Nat.mul_1_r 2).
           rewrite <- (Nat.add_assoc (2*k) 1 1 ).
           rewrite -> (Nat.add_1_r 1).
           reflexivity.
           
        ** exact (H (H_not_even H_n)).
           

   - intro H_S_n.
      rewrite <- (Nat.add_1_r n').
      assert (H_n : is_even n' = true).
          
      + exact (predecessor_of_not_even_is_even n' H_S_n).

      + Check (is_even).

        assert (H : (exists k : nat, 2 * k = n') -> (exists t : nat, S (2 * t) = n' + 1)).

        ** intro H_k.
           destruct H_k as [k H_S_k].
           exists k.
           rewrite -> H_S_k.
           rewrite -> (Nat.add_1_r n').
           reflexivity.

        ** exact (H (H_even H_n)).

   * destruct both as [emente _]. 
     exact emente. 
Qed.


(*

 Find better name for this lemma.

 even + even = even.
 not_even + not_even = even.

 So we a function that returns true
 if the inputs are the same, which
 is the negation of XOR.

 There are other ways to express
 this, but we are familar with
 mainpulating negb and xorb from
 the mystery function exercises

 ---

 In retrospect this approach scales
 terribly when considering things like
 division by 3.

 You need to come up with a logical
 circuit that returns true for n out
 of 2^n cases.

 For our proof we simply need
 (is_even a = true) ->
   (is_even b = true) ->
     (is_even (a + b) = true)

TODO : Write the proof with the simpler
lemma mentioned above.

*)

Lemma sum_is_even:
  forall a b : nat,
    is_even (a + b) = negb (xorb (is_even a) (is_even b)).

Proof.
  intros a.
  induction a as [ | a' IHa].

  * intro b.
    rewrite -> (Nat.add_0_l b).
    rewrite -> fold_unfold_is_even_0.
    Search (xorb _ true).
    rewrite -> (xorb_true_l (is_even b)).
    Search (negb (negb _)).
    rewrite -> (negb_involutive (is_even b)).
    reflexivity.

  * intro b.
    induction b as [ | b' IHb'].

    -  rewrite -> (Nat.add_0_r (S a')).
       rewrite -> fold_unfold_is_even_0.
       rewrite -> (xorb_true_r (is_even (S a'))).
       rewrite -> (negb_involutive (is_even (S a'))).
       reflexivity.

    -  rewrite -> (predecessor_flips_evenness b').
       Search (xorb _ (negb _)).
       rewrite <- (negb_xorb_r (is_even (S a')) (is_even b')).
       rewrite <- IHb'.

       rewrite <- (Nat.add_1_l b').
       Search (_ + (_ + _)).
       rewrite -> (Nat.add_shuffle3 (S a') 1 b').
       rewrite -> (Nat.add_1_l (S a' + b')).
       rewrite -> (successor_flips_evenness (S a' + b')).
       rewrite -> (negb_involutive (is_even (S (S a' + b')))).
       reflexivity.

Qed.

Theorem even_times_natural_is_even:
  forall a b : nat,
    (is_even a = true) ->
        (is_even (a*b) = true).

Proof.
  intros a b H_a.

  assert (H_a_double := (even_is_two_times_natural a H_a)).
  destruct H_a_double as [t H_a_double].
  
  rewrite <- (H_a_double).

  Search (_ * _ * _).
  rewrite <- (Nat.mul_assoc 2 t b).

  rewrite -> (two_times_natural_is_even (t * b)).
  reflexivity.
Qed.  

(*

  Simple exercise

*)
  
Theorem the_product_of_two_consecutive_natural_numbers_is_even:
  forall n : nat,
    is_even (n * (S n)) = true.


Proof.
  intro n.
  induction n as [ | n' IHn'].

  * rewrite -> (Nat.mul_0_l 1).
    rewrite -> fold_unfold_is_even_0.
    reflexivity.

  * rewrite <- (Nat.add_1_l (S n')).
    rewrite <- (Nat.add_1_l n') at 2.
    rewrite -> (Nat.add_assoc 1 1 n').
    rewrite -> (Nat.add_1_l 1).
    Search (_ * (_ + _)).
    rewrite -> (Nat.mul_add_distr_l (S n') 2 n').
    rewrite -> (sum_is_even (S n' * 2) (S n' * n')).
    rewrite -> (Nat.mul_comm (S n') n').
    rewrite -> (Nat.mul_comm (S n') 2).
    rewrite -> IHn'.
    rewrite -> (two_times_natural_is_even (S n')).
    simpl.
    reflexivity.
Qed.


(*

  Excercise 15

  We use the argument a primary school boy
  would use.

  We have shown all the properties I once
  thought was "obvious".

  We already know n*(S n) is even, so n*(S n)*(S (S n)) is
  even because even times even is even.
  
*)

Theorem the_product_of_three_consecutive_natural_numbers_is_even:
  forall n : nat,
    is_even (n * (S n) * (S (S n))) = true.

Proof.
  intro n. 
  Check (the_product_of_two_consecutive_natural_numbers_is_even n).

  exact (even_times_natural_is_even
           (n * S n)
           (S (S n))
           (the_product_of_two_consecutive_natural_numbers_is_even n)).

Qed.


  





    

(* 
   In general we can show (n + k)!/(n - 1)! is divisible
   by k! for all n, for all k greater than or equal to 1.

   You would do this by induction on k and using the property
   that even times a natural number is even.

   This would make light work of each and every one of the
   exercises.

   We can first try the exercises out the "standard" way
   and then resort to this.
*)




