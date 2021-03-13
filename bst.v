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

(* Proofs *)
Theorem insertBST : forall t : tree, forall n : nat, bst t -> bst (insert n t).

Theorem sortPreservesBST : forall t : tree, bst (sort t).

Theorem occursBST : forall n : nat, forall t : tree, occurs n t <-> occurs n (sort t).




