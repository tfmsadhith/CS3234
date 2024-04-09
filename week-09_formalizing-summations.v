(* week-09_formalizing-summations.v *)
(* LPP 2024 - CS3234 2023-2024, Sem2 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of Fri 22 Mar 2024 *)

(* ********** *)

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


Check Sigma.

Compute Sigma 10 (fun x : nat => x * x).


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

(* ***** *)

Lemma about_factoring_a_multiplicative_constant_on_the_right_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => f i * c) = Sigma x f * c.

Proof.
  intros x c f.
  revert c.

  induction x as [ | x' IHx'].

  * intros c.
    rewrite ->2 fold_unfold_Sigma_O.
    reflexivity.

  * intros c.
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    Search ((_ + _) * _ = _ * _ + _ *_).
    rewrite -> (Nat.mul_add_distr_r).
    reflexivity.
Qed.    
    
(* ***** *)

(*
  It would be possible to write this using
  the previous lemma if we could manipulate
  the terms inside (fun i => c * f i).

  Since we cannot "intro" anything for i
  when it is inside of a function, we are
  stuck
*)

Lemma about_factoring_a_multiplicative_constant_on_the_left_in_Sigma :
  forall (x c : nat)
         (f : nat -> nat),
    Sigma x (fun i => c * f i) = c * Sigma x f.

Proof.
  intros x c f.
  revert c.

  induction x as [ | x' IHx'].

  * intros c.
    rewrite ->2 fold_unfold_Sigma_O.
    reflexivity.

  * intros c.
    rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    rewrite -> (Nat.mul_add_distr_l).
    reflexivity.
Qed.
    
(* ***** *)


(* ***** *)

Lemma about_swapping_Sigma :
  forall (x y : nat)
         (f : nat -> nat -> nat),
    Sigma x (fun i => Sigma y (fun j => f i j)) = Sigma y (fun j => Sigma x (fun i => f i j)).

Proof.
  intros x y f.
  revert y.

  induction x as [ | x' IHx'].

  * intros y.
    rewrite -> fold_unfold_Sigma_O.
    simpl (fun j : nat => Sigma 0 (fun i : nat => f i j)).
    (* Ah, so we have a way to handle terms
       inside functions *)
    reflexivity.

  * intros y.
    rewrite -> fold_unfold_Sigma_S.
    rewrite -> IHx'.

    (*
      Whenever we have to deal with the
      function inside of the sigma function,
      we seem to always need to do things
      via induction.

      Again, this is because of a lack of
      "intros".

      On a deeper level, this is revealing the
      assumptions we make in pen and paper
      mathematics that we typically take for
      granted.
    *)

    induction y as [ | y' IHy'].

  - rewrite ->3 fold_unfold_Sigma_O.
    rewrite ->fold_unfold_Sigma_S.
    reflexivity.

  - rewrite ->4 fold_unfold_Sigma_S.
    rewrite <- IHy'.
    (* Associatve-commutative rewriting *)
    
    Search (_ + (_ + _) = _ + (_ + _)).
    rewrite -> Nat.add_shuffle3.
    rewrite <- Nat.add_assoc.
    rewrite -> Nat.add_shuffle3.
    rewrite -> Nat.add_assoc.

    Show Proof.
    reflexivity.
Qed.    
    
    
(* ***** *)

Lemma about_Sigma_with_two_equivalent_functions :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        f i = g i) ->
    Sigma x f = Sigma x g.

Proof.
  intros x f g i.

  (*
    Induction on x makes the most sense because
    the structurally inductive definition we are
    dealing with uses x to know how many times
    it has to repeat.
   *)

  induction x as [ | x' IHx'].

  * rewrite ->2 fold_unfold_Sigma_O.
    rewrite -> i.
    reflexivity.

  * rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> i.
    rewrite -> IHx'.
    reflexivity.
Qed.    
  
(* ***** *)

Lemma about_Sigma_with_two_equivalent_functions_up_to_the_bound :
  forall (x : nat)
         (f g : nat -> nat),
    (forall i : nat,
        i <= x ->
        f i = g i) ->
    Sigma x f = Sigma x g.

Proof.
  (*
    The stand-alone proof is easy but there's
    no fun in that.

    Now if the two functions are equivalent up
    to the bound, shouldn't we find a way to use
    our old lemma?
   *)

  intros x f g H_i_le_x.
  (*
    If we can consider the case when i <= x and
    also the case when i > x, we should be able to
    ruse the first lemma for the first case and
    derive an absurdity for the second case.

    After typing this out, it is clear that playing
    with the domain in these ways uses a lot more
    lemmas than previously thought.
   *)

  induction x as [ | x' IHx'].

  * rewrite ->2 fold_unfold_Sigma_O.
    Search (_ <= _).
    rewrite -> (H_i_le_x 0 (le_n 0)).
    (* Lemmas given arguments to prevent random goal generation *)
    reflexivity.

  * rewrite ->2 fold_unfold_Sigma_S.
    rewrite -> (H_i_le_x (S x') (le_n (S x'))).

    (* TODO:

       Fix the names here into something clear.
       H is used twice here.
     *)
    assert (H : forall i : nat, i <= x' -> f i = g i).

    - intros i.

      Search (_ <= _ -> _ <= S _).
      intros H.
      exact (H_i_le_x i (Nat.le_le_succ_r i x' H)).

   - rewrite -> (IHx' H).
     reflexivity.
  Qed.

    
    
(* ***** *)

Lemma about_Sigma_with_an_additive_function :
  forall (x : nat)
         (f g : nat -> nat),
    Sigma x (fun i => f i + g i) = Sigma x f + Sigma x g.

Proof.
  intros x f g.

  induction x as [ | x' IHx'].

  * rewrite ->3 fold_unfold_Sigma_O.
    reflexivity.

  * rewrite ->3 fold_unfold_Sigma_S.
    rewrite -> IHx'.
    rewrite <- Nat.add_assoc.
    rewrite -> (Nat.add_shuffle3 (Sigma x' g)).
    rewrite -> Nat.add_assoc.
    reflexivity.
Qed.    

(* ***** *)

Lemma about_Sigma_with_a_constant_function :
  forall x y : nat,
    Sigma x (fun _ => y) = y * (S x).

(* In plain english, this is saying that
   if you sum a number y, (S x) times, you
   get y * (S x).

   In this lemma we are basically showing
   the elementary school idea that multiplication
   is nothing more than repeated addition.
 *)
   

Proof.
  intros x.
  (* Again we choose to induct on x and not y
     because x is what tells us how many times
     we need to repeat something *)

  induction x as [ | x' IHx'].

  * intros y.
    rewrite -> fold_unfold_Sigma_O.
    rewrite -> (Nat.mul_1_r).
    reflexivity.

  * intros y.
    rewrite -> (fold_unfold_Sigma_S).
    rewrite -> IHx'.
    (* Elementary algebra *)
    rewrite -> (mult_n_Sm y (S x')).
    reflexivity.
Qed.    
    
Lemma about_Sigma_with_two_small_a_function :
  forall (x : nat)
         (f : nat -> nat),
    (forall i : nat,
        i <= x ->
        f i = 0) ->
    Sigma x f = 0.

(*
   Simply put, this is saying that
   if you add zero up for any finite
   number of times, you still get
   zero.
*)

Proof.
  intros x f H_i_le_x.

  induction x as [ | x' IHx'].

  * rewrite -> fold_unfold_Sigma_O.
    rewrite -> (H_i_le_x 0 (le_n 0)).
    reflexivity.

    (* TODO:

       If there is a better name than H...
     *)
  * rewrite -> fold_unfold_Sigma_S.
    assert (H : forall i : nat, i <= x' -> f i = 0).

  - intros i H.
    exact (H_i_le_x i (Nat.le_le_succ_r i x' H)).

  - rewrite -> (IHx' H).
    rewrite -> (H_i_le_x (S x') (le_n (S x'))).
    rewrite -> (Nat.add_0_r).
    reflexivity.

(*
    Stand alone proof out of the way,
    we observe that this is a special case
    of the constant function.

    But due to the issues with fun and forall,
    we are unable to prove this as so. Another
    case where a classic pen and paper argument
    cannot be translated easily into tCPA.

    Possibly this means something is assumed
    in the pen and paper argument that is not
    made clear...

    HINDSIGHT: Okay, now we can use our special
    case of the axiom of functional extensionality.

 *)

    Restart.
    intros x f H_i_le_x.

    assert (H := (about_Sigma_with_two_equivalent_functions_up_to_the_bound
             x
             f
             (fun _ : nat => 0)
             H_i_le_x
          )).

    rewrite -> H.
    Check about_Sigma_with_a_constant_function.
    rewrite -> about_Sigma_with_a_constant_function.
    rewrite -> Nat.mul_0_l.
    reflexivity.
Qed.

    
  
(* ***** *)

(*

Was this a repeat?

Lemma about_Sigma_with_two_small_a_function :
  forall (x : nat)
         (f : nat -> nat),
    (forall i : nat,
        i <= x ->
        f i = 0) ->
    Sigma x f = 0.
Proof.
Abort.
 *)


(* ***** *)

Lemma about_Sigma_up_to_a_positive_sum :
  forall (x y : nat)
         (f : nat -> nat),
    Sigma (x + S y) f = Sigma x f + Sigma y (fun i => f (x + S i)).

(*
  This basically "associativity on steroids".
*)

Proof.
  intros x y f.
  revert y.

  induction x as [ | x' IHx'].

  (*
    Because we need to induct everytime
    we need to deal with fun, we need the
    double induction
   *)

  * intros y.
    rewrite -> (Nat.add_0_l (S y)).
    rewrite -> (fold_unfold_Sigma_S).
    rewrite -> (fold_unfold_Sigma_O).
    simpl (fun i : nat => f (0 + S i)).

    induction y as [ | y' IHy'].

    - rewrite ->2 (fold_unfold_Sigma_O).
      reflexivity.

    - rewrite ->2 (fold_unfold_Sigma_S).
      rewrite ->IHy'.
      rewrite -> (Nat.add_assoc).
      reflexivity.

  * intros y.
    rewrite -> (fold_unfold_Sigma_S).
    rewrite <- (Nat.add_1_l x') at 1.
    rewrite <- (Nat.add_assoc).
    rewrite -> (Nat.add_1_l (x' + S y)).
    rewrite -> (fold_unfold_Sigma_S).
    rewrite -> IHx'.
    rewrite <- (Nat.add_assoc).
    rewrite <- (Nat.add_1_l (x' + S y)).
    rewrite -> (Nat.add_assoc 1 x' (S y)).
    rewrite -> (Nat.add_1_l x').
    (* Simplify as much as we can here,
       so the nested induction does not
       devolve into a mess *)
    
    induction y as [ | y' IHy'].

    - rewrite ->2 (fold_unfold_Sigma_O).
      rewrite -> (Nat.add_1_r x').
      rewrite -> (Nat.add_assoc).
      reflexivity.

    - rewrite ->2 (fold_unfold_Sigma_S).
      rewrite <- (Nat.add_1_l (S y')).
      rewrite -> (Nat.add_assoc x').
      rewrite -> (Nat.add_1_r x').
      rewrite ->4 (Nat.add_assoc).
      rewrite <- IHy'.
      rewrite -> (Nat.add_assoc).
      reflexivity.
Qed.
      
 
      
        
(* ***** *)

Lemma about_Sigma_specifically_left :
  forall (x y : nat)
         (f : nat -> nat),
    Sigma (x * S y + y) f = Sigma x (fun i => Sigma y (fun j => f (i * S y + j))).

Proof.
  intros x y f.
  revert y.

  induction x as [ | x' IHx'].

  * intros y.
    simpl (0 * S y + y).
    rewrite -> (fold_unfold_Sigma_O).
    rewrite -> (Nat.mul_0_l).
    assert (H : forall j : nat, f (0 + j) = f (j)).
    {
      intros j.
      rewrite -> Nat.add_0_l.
      reflexivity.
    }
    exact (about_Sigma_with_two_equivalent_functions
           y
           f
           (fun j : nat => f (0 + j))
           H
          ).
        
  * intros y.
    assert (H : S x' * S y + y = x' * S y + y + S y).
    {
      simpl.
      rewrite <- (Nat.add_1_r y) at 3.
      rewrite -> (Nat.add_assoc).
      rewrite -> (Nat.add_1_r).
      rewrite <- (Nat.add_assoc).
      rewrite -> (Nat.add_comm).
      reflexivity.
    }
    rewrite -> H.
    rewrite -> about_Sigma_up_to_a_positive_sum.
    rewrite -> IHx'.
    rewrite -> (fold_unfold_Sigma_S).

    assert (J : Sigma y (fun i : nat => f (x' * S y + y + S i)) = Sigma y (fun j : nat => f (S x' * S y + j))).
    {
      Check about_Sigma_with_two_equivalent_functions.
      assert (K : forall i : nat,
                 (fun j : nat => f (x' * S y + y + S j))(i)
               = (fun j : nat => f (S x' * S y + j))(i)).
      {
        intros t.
        simpl (S x' * S y + t).
        assert (L : x' * S y + y + S t = S (y + x' * S y + t)).
        {
          rewrite -> plus_n_Sm.
          rewrite -> Nat.add_comm.
          rewrite -> (Nat.add_comm _ y).
          rewrite -> (Nat.add_comm).
          reflexivity.
          
        }
        rewrite -> L.
        reflexivity.
      }
      exact  (about_Sigma_with_two_equivalent_functions
             y
             (fun i : nat => f (x' * S y + y + S i))  
             (fun j : nat => f (S x' * S y + j))
             K
            ).
      }
    rewrite -> J.
    reflexivity.
Qed.

Lemma about_Sigma_up_to_a_positive_product_left :
  forall (x y : nat)
         (f : nat -> nat),
    Sigma (S x * S y) f = Sigma (x * S y + y) f + f (S x * S y).

Proof.
  intros x y f.

  assert (H : S x * S y = S(x*(y + 1) + y)).
  {
   simpl.
   rewrite -> (Nat.add_1_r y).
   rewrite -> (Nat.add_comm).
   reflexivity.
  }
  rewrite -> H.
  rewrite -> fold_unfold_Sigma_S.
  rewrite -> Nat.add_1_r.
  reflexivity.
Qed.


(* ********** *)

Definition Sigma1 (n : nat) (f : nat -> nat) : nat :=
  match n with
    O =>
    0
  | S n' =>
    Sigma (S n') f
  end.

Lemma fold_unfold_Sigma1_O:
  forall (f : nat -> nat),
    Sigma1 O f = 0.

Proof.
  fold_unfold_tactic Sigma1.
Qed.

Lemma fold_unfold_Sigma1_S:
  forall (n' : nat)
         (f : nat -> nat),
         Sigma1 (S n') = Sigma (S n').

Proof.
  fold_unfold_tactic Sigma1.
Qed.  

(* ***** *)

Property about_Sigma1 :
  forall f : nat -> nat,
    f 0 = 0 ->
    forall n : nat,
      Sigma1 n f = Sigma n f.

(* Sigma 1 doesn't add f(0)
   while Sigma adds f(0). *)

Proof.
  intros f H_f_0 n.
  induction n as [ | n' IHn'].

  * rewrite -> fold_unfold_Sigma1_O.
    rewrite -> fold_unfold_Sigma_O.
    rewrite -> H_f_0.
    reflexivity.

  * rewrite -> (fold_unfold_Sigma1_S n' f).
    rewrite -> (fold_unfold_Sigma_S n' f).
    reflexivity.
Qed.    
    
    
(* end of week-09_formalizing-summations.v *)
