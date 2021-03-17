Require Import Datatypes.
Require Import Arith.
Require Import Nat.
Require Import List.
Require Import Omega.

(* Definition of basic binary tree *)
Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

(* All node keys in (sub)tree are less than a fixed value *)
Fixpoint lessTree (T : tree) (n : nat) : Prop :=
  match T with
  | leaf => True
  | node lt k rt => (k < n) /\ (lessTree lt n) /\ (lessTree rt n)
end.

(* All node keys in (sub)tree are greater than a fixed value *)
Fixpoint grtTree (T : tree) (n : nat) : Prop :=
  match T with
  | leaf => True
  | node lt k rt => (k > n) /\ (grtTree lt n) /\ (grtTree rt n)
end.

(* BST property *)
Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node lt k rt => (bst lt) /\ (bst rt) /\ (lessTree lt k) /\ (grtTree rt k)
end.

(* Insert function for a binary search tree *)
Fixpoint insert (n : nat) (T : tree) : tree :=
  match T with
  | leaf => (node leaf n leaf)
  | node lt k rt => match (compare k n) with 
      | Eq => T
      | Lt => (node lt k (insert n rt))
      | Gt => (node (insert n lt) k rt)
  end
end.

(* Transform a regular binary tree into a list *)
Fixpoint treeToList (T : tree) : list nat :=
  match T with
  | leaf => nil
  | node lt k rt => cons k ((treeToList lt) ++ (treeToList rt))
end.

(* Transforms a list into a BST *)
Fixpoint listToBST (L : list nat) : tree :=
  match L with
  | nil => leaf
  | cons n ns => (insert n (listToBST ns))
end.

(* Transforms a tree into a BST *)
Definition sort (T : tree) : tree := listToBST(treeToList T).

(* Checks that an element occurs in a tree *)
Fixpoint occurs (n : nat) (T : tree) : Prop :=
  match T with
  | leaf => False
  | node lt k rt => (k = n) \/ (occurs n lt) \/ (occurs n rt)
end.


(* Proofs for Part 1 *)

(* Auxiliary proof that inserting n > n0 into a BST with all elements < n0 preserves the inequality *)
Theorem grtPreserveBST : forall t : tree, forall n0 : nat, forall n : nat,
  (grtTree t n0) /\ n > n0 -> (grtTree (insert n t) n0).
Proof.
intros.
destruct H.
induction t.
-
simpl.
auto.
-
simpl.
case (compare n1 n).
(* Current node *)
simpl.
simpl in H.
trivial.
(* Right subtree (greater) *)
simpl.
simpl in H.
intuition. (* Each disjunct corresponds to a conclusion *)

(** Complete proof:
split.
destruct H.
trivial.

split.
destruct H.
destruct H1.
trivial.

destruct H.
apply IHt2.
destruct H1.
trivial. *)
(* Left subtree (less) *)
simpl.
simpl in H.
intuition.

(** Complete proof:
split.
destruct H.
trivial.

split.
destruct H.
destruct H1.
apply IHt1.
trivial.

destruct H.
destruct H1.
trivial. *)
Qed.

(* Analog proof for n < n0 *)
Theorem lessPreserveBST : forall t : tree, forall n0 : nat, forall n : nat, 
  (lessTree t n0) /\ n < n0 -> (lessTree (insert n t) n0).
Proof.
intros.
destruct H.
induction t.
-
simpl.
auto.
-
simpl.
case (compare n1 n).
(* Current node *)
simpl.
simpl in H.
intuition.
(* Right subtree (greater) *)
simpl.
simpl in H.
intuition.
(* Left subtree (less) *)
simpl.
simpl in H.
intuition.
Qed.

Theorem insertBST : forall t : tree, forall n : nat, bst t -> bst (insert n t).
Proof.
intros.
induction t.
- 
simpl.
auto.
- 
simpl.
case (compare n0 n) eqn:Heqe.

simpl.
split.
simpl in H.
destruct H.
intuition.
split.
simpl in H.
intuition.
split.
simpl in H.
intuition.
simpl in H.
intuition.

simpl in H.
split.
intuition.

split.
apply IHt2.
intuition.
split.
intuition.

apply nat_compare_lt in Heqe.
assert (grtTree t2 n0 /\ n > n0).
intuition.
apply grtPreserveBST in H0.
intuition.

simpl.
split.
apply IHt1.
simpl in H.
intuition.

simpl in H.
firstorder.
apply lessPreserveBST.
intuition.
apply nat_compare_gt in Heqe.
intuition.
Qed.


Theorem sortPreservesBST : forall t : tree, bst (sort t).
Admitted.



Theorem insertPreservation : forall t : tree, forall n : nat, forall a : nat, occurs n t \/ n = a <-> occurs n (insert a t).
Proof.
unfold iff. 
split.
intros.
- (* => *)
induction t.
(* Base case *)
simpl.
intuition.
(* Step case *)
simpl.
case (compare n0 a) eqn:Heqe1.
(* Current node *)
simpl.
case (compare n0 n) eqn:Heqe2.
apply nat_compare_eq in Heqe2.
intuition.
apply nat_compare_lt in Heqe2.
intuition.
apply nat_compare_eq in Heqe1.
intuition.
destruct H.
simpl in H.
destruct H.
intuition.
destruct H.
right.
left.
trivial.
right.
right.
trivial.
intuition.
right.
left.
apply nat_compare_gt in Heqe2.
apply nat_compare_eq in Heqe1.
omega.
(* Right subtree (greater) *)
simpl.
case (compare n0 n) eqn:Heqe2.
intuition.
apply nat_compare_eq in Heqe2.
left.
trivial.
destruct H.
simpl in H.
intuition.
right.
right.
apply IHt2.
right.
trivial.
intuition.
simpl in H0.
intuition.
(* Left subtree (less) *)
simpl.
case (compare n0 n) eqn:Heqe2.
intuition.
apply nat_compare_eq in Heqe2.
left.
trivial.
destruct H.
simpl in H.
intuition.
right.
left.
apply IHt1.
right.
trivial.
intuition.
simpl in H0.
intuition.

- (* <= *)
intros.
induction t.
(* Base case *)
simpl in H.
intuition.
(* Step case *)
simpl in H.
case (compare n0 a) eqn:Heqe1 in H.
simpl in H.
case (compare n0 n) eqn:Heqe2 in H.
right.
apply nat_compare_eq in Heqe1.
apply nat_compare_eq in Heqe2.
omega.

left.
simpl.
trivial.
left.
simpl.
trivial.
simpl in H.
case (compare n0 n) eqn:Heqe2 in H.
left.
simpl.
apply nat_compare_eq in Heqe2.
left.
trivial.
intuition.

apply nat_compare_lt in Heqe2.
intuition. (* contradiction *)

left.
simpl.
right.
left.
trivial.

left.
simpl.
right.
right.
trivial.

left.
simpl.
intuition.
apply nat_compare_lt in Heqe1.
apply nat_compare_gt in Heqe2.
intuition. (* contradiction *)

simpl in H.
case (compare n0 n) eqn:Heqe2 in H.
left.
simpl.
apply nat_compare_eq in Heqe2.
left.
trivial.
destruct H.
apply nat_compare_lt in Heqe2.
intuition.
destruct H.
destruct IHt1.
apply H.
left.
simpl.
apply nat_compare_lt in Heqe2.
right.
left.
apply H0.
right.
apply H0.
left.
simpl.
apply nat_compare_lt in Heqe2.
right.
right.
apply H.
destruct H.
apply nat_compare_gt in Heqe2.
intuition. (* contradiction *)
destruct H.
destruct IHt1.
apply H.
left.
simpl.
right.
intuition.
intuition.
left.
simpl.
right.
right.
apply H.
Qed.


Theorem occursBSTfromList : forall n : nat, forall l : list nat, In n l <-> occurs n (listToBST l).
Proof.
intros.
unfold iff.
split.
-
intros.
induction l.
(* Base case *)
simpl.
intuition.
(* Step case *)
simpl.
simpl in H.
apply insertPreservation.
destruct H.
right.
intuition.
apply IHl in H.
left.
apply H.
-
intros.
induction l.
(* Base case *)
intuition.
(* Step case *)
simpl.
simpl in H.
apply insertPreservation in H.
destruct H.
apply IHl in H.
right.
apply H.
left.
intuition.
Qed.

Theorem occursBST : forall n : nat, forall t : tree, occurs n t <-> occurs n (sort t).
Proof.
intros.
unfold iff.
split.
- (* '=>' *)
intros.
induction t.
(* Base case *)
simpl.
intuition.
(* Step case *)
unfold sort.
Admitted.






















