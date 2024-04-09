Require Import List.
Require Import Arith Nat Bool.
Ltac fold_unfold_tactic name := intros; unfold name; fold name; reflexivity.


Inductive binary_tree (V : Type) : Type :=
  Leaf : V -> binary_tree V
| Node : binary_tree V -> binary_tree V -> binary_tree V.

(* Program to flatten a binary tree into a list.
   I am aware that the paper does not specify a
   binary tree, but I don't think that is the
   kernel of the idea being considered *)

Fixpoint flatten_binary_tree (V : Type) (t : binary_tree V) (a : list V): (list V) :=
  match t with
  | Leaf _ n =>
    (n :: a)
  | Node _ t1 t2 =>
    flatten_binary_tree V t1 (flatten_binary_tree V t2 a)
  end.

(* Okay, so we see that this is not tail-recursive,
   but we have used the accumulator pattern here.

   It was not obvious in the first place that accumulators
   and tail-recursive programs were related at a deep level.
 *)

Compute flatten_binary_tree nat (Node nat (Leaf nat 3)
                                          (Leaf nat 3)) (nil).
Compute flatten_binary_tree nat (Node nat (Node nat
                                             (Leaf nat 3)
                                             (Leaf nat 1))
                                          (Node nat
                                             (Leaf nat 3)
                                             (Leaf nat 4))) nil.

Compute flatten_binary_tree nat (Node nat (Node nat
                                             (Node nat
                                                (Leaf nat 4)
                                                (Leaf nat 5))
                                             (Leaf nat 4))
                                          (Leaf nat 3)).


Fixpoint primitive_iteration_over_nats (n : nat)
                                       (W : Type) (z : W) (s : W -> W) : W :=
  match n with
    | O =>
      z
    | S n' =>   
      s (primitive_iteration_over_nats n' W z s)
  end.


Lemma fold_unfold_primitive_iteration_over_nats_O:
  forall (W : Type)
         (z : W)
         (s : W -> W),
         primitive_iteration_over_nats 0 W z s = z.

Proof.
  fold_unfold_tactic primitive_iteration_over_nats.
Qed.

Lemma fold_unfold_primitive_iteration_over_nats_S:
  forall (n' : nat)
         (W : Type)
         (z : W)
         (s : W -> W),
         primitive_iteration_over_nats (S n') W z s 
       = s (primitive_iteration_over_nats n' W z s).                                
Proof.
  fold_unfold_tactic primitive_iteration_over_nats.
Qed.
  
(* Okay, so this is just letting you fiddle with the successor and base functions. With this you could easily generate the list of all even numbers, arithmetic progressions, geometric progressions, etc.

  TODO : Figure out if you can write a function that sums up all the primes.
 *)

(* Odd numbers *)
Compute primitive_iteration_over_nats 0 nat 1 (fun x : nat => 2 + x).
(* Powers of two *)
Compute primitive_iteration_over_nats 0 nat 1 (fun x : nat => 2 * x).

(*
   TODO : Prove that it is not possible to write a function that sums up all the primes with primitive iteration
*)

Fixpoint primitive_recursion_over_nats (n : nat)
                                       (W : Type) (z : W) (s : nat -> W -> W) : W :=
  match n with
  | 0 =>
    z
  | S n' =>   
    s n' (primitive_recursion_over_nats n' W z s)
  end.

(* With an index, we can generate polynomials and the like much more easily *)

Fixpoint primitive_iteration_over_lists (V : Type)
                                        (vs : list V)
                                        (W : Type)
                                        (n : W)
                                        (c : V -> W -> W)
                                        : W :=
  match vs with
  | nil =>
    n
  | v :: vs' =>
    c v (primitive_iteration_over_lists V vs' W n c)
  end.

Lemma fold_unfold_primitive_iteration_over_lists_nil:
  forall (V : Type)
         (W : Type)
         (n : W)
         (c : V -> W -> W),
    primitive_iteration_over_lists V nil W n c = n.

Proof.
  fold_unfold_tactic primitive_iteration_over_lists.
Qed.            

Lemma fold_unfold_primitive_iteration_over_lists_cons:
  forall (V : Type)
         (vs' : list V)
         (W : Type)
         (n : W)
         (c : V -> W -> W)
         (v : V),
    primitive_iteration_over_lists V (v :: vs') W n c =
    c v (primitive_iteration_over_lists V vs' W n c).

Proof.
  fold_unfold_tactic primitive_iteration_over_lists.
Qed.


(* You have access to the thing you are adding, we didn't have that when doing primitive iteration over the naturals... *)

Compute primitive_iteration_over_lists nat nil nat 232 (fun x v : nat => x + 2).

Definition list_of_units_from_nat (n : nat) : list unit :=
  primitive_iteration_over_nats n (list unit) nil (fun us => tt :: us).

Definition nat_from_list_of_units (us : list unit) : nat :=
  primitive_iteration_over_lists unit us nat 0 (fun _ i => S i).

(*

"That list_of_units_from_nat (defined in Sec. 1.1.1) and nat_from_list_of_units are inverses of each other is proved by induction, which establishes the isomorphism between nat and list unit mentioned in the opening sentence"

*)

Check unit.


Theorem list_of_units_from_nat_and_nat_from_list_of_units_are_inverses :
  forall (n : nat)
         (us : list unit),
         nat_from_list_of_units (list_of_units_from_nat n) = n
         /\
         list_of_units_from_nat (nat_from_list_of_units us) = us.

Check tt.

Proof.
  intros n us.
  unfold nat_from_list_of_units, list_of_units_from_nat.
  split.

  - induction n as [ | n' IHn'].
  
    * rewrite -> fold_unfold_primitive_iteration_over_nats_O.
      rewrite -> fold_unfold_primitive_iteration_over_lists_nil.
      reflexivity.

    * rewrite -> fold_unfold_primitive_iteration_over_nats_S.
      rewrite -> fold_unfold_primitive_iteration_over_lists_cons.
      rewrite -> IHn'.
      reflexivity.

  - induction us as [ | [] us' IHus'].
    
    * rewrite -> fold_unfold_primitive_iteration_over_lists_nil.
      rewrite -> fold_unfold_primitive_iteration_over_nats_O.
      reflexivity.

    * rewrite -> fold_unfold_primitive_iteration_over_lists_cons.
      rewrite -> fold_unfold_primitive_iteration_over_nats_S.
      rewrite -> IHus'.
      reflexivity.
Qed.

(* If an operation is left-permutative, then is has to be associative and commutative *)

Definition is_left_permutative (V W : Type) (op2 : V -> W -> W) :=
  forall (v1 v2 : V)
         (v3 : W),
    op2 v1 (op2 v2 v3) = op2 v2 (op2 v1 v3).
    

Theorem left_permuativity_implies_associativity_and_commutativity :
  forall (V : Type) (f : V -> V -> V),
    (forall (v1 v2 : V),
      f v1 v2 = f v2 v1) ->
    (forall (v1 v2 v3 : V),
        f v1 (f v2 v3) = f (f v1 v2) v3) ->
          is_left_permutative V V f.


Proof.
  unfold is_left_permutative.
  intros V f H_comm H_assoc.

  intros v1 v2 v3.

  rewrite -> H_comm.
  rewrite <- (H_assoc v2 v3 _).
  rewrite -> (H_comm v3 v1).
  reflexivity.
Qed.

Fixpoint primitive_recursion_over_lists (V : Type) (vs : list V) (W : Type) (n : W) (c : V -> list V -> W -> W) : W :=
  match vs with
  | nil => n
  | v :: vs' => c v vs' (primitive_recursion_over_lists V vs' W n c)
  end.                



Definition nat_pred_naive (n : nat) : nat :=
  match n with
  | O => 0 (* This is a tricky thing *)
  | S n' => n'         
  end.

Compute nat_pred_naive 12.

(* We can easily calculate the primitive program.
   It is clear that n' has to be used. Thus we favour
   recursion.

   Since we know the base case and the function that
   we need that operates on n' (literally just return
   n' and be done with it)
*)



Check (primitive_recursion_over_nats).

(* b is what we have gathered up thus far,
   a is what we will be getting in the next
   iteration *)

Definition nat_pred_pr (n : nat) : nat :=
  primitive_recursion_over_nats n nat 0 (fun a b : nat => a).

Compute nat_pred_pr 0.
Compute nat_pred_pr 1.
Compute nat_pred_pr 2.
Compute nat_pred_pr 2322.
Compute nat_pred_pr 123.
Compute nat_pred_pr 17233.
Compute nat_pred_pr 73.


(* Alas, there is no constant time function
   for predecessors here

   From the expression:

   (primitive_iteration_over_nats n’ W z s).

   I want to get the n' out as easily as I can,
   by applying a function to the expression.

   The function could just add 1?

*)




