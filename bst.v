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