Require Import Datatypes.
Require Import Arith.
Require Import Nat.
Require Import List.
Require Import Omega.
Require Import Lia.

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
- (* Base case *)
simpl.
auto.
- (* Step case *)
simpl.
case (compare n1 n).
+ simpl.
  simpl in H.
  trivial.
+ simpl.
  simpl in H.
  intuition.
+ simpl.
  simpl in H.
  intuition.
Qed.

(* Analog proof for n < n0 *)
Theorem lessPreserveBST : forall t : tree, forall n0 : nat, forall n : nat, 
  (lessTree t n0) /\ n < n0 -> (lessTree (insert n t) n0).
Proof.
intros.
destruct H.
induction t.
- (* Base case *)
simpl.
auto.
- (* Step case *)
simpl.
case (compare n1 n).
+ simpl.
  simpl in H.
  trivial.
+ simpl.
  simpl in H.
  intuition.
+ simpl.
  simpl in H.
  intuition.
Qed.


Theorem insertBST : forall t : tree, forall n : nat, bst t -> bst (insert n t).
Proof.
intros.
induction t; simpl.
- (* Base case *)
auto.
- (* Step case *)
case (compare n0 n) eqn:Heqe.
+ simpl.
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
+ simpl in H.
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
+ simpl.
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


Theorem insertPreservation : forall t : tree, forall n : nat, forall a : nat, occurs n t \/ n = a <-> occurs n (insert a t).
Proof.
unfold iff.
split; intros.
- (* => *)
induction t; simpl.
(* Base case *)
intuition.
(* Step case *)
case (compare n0 a) eqn:Heqe1; simpl.
(* Current node *)
+ case (compare n0 n) eqn:Heqe2.
  apply nat_compare_eq in Heqe2.
  intuition.
  apply nat_compare_lt in Heqe2.
  intuition.
  apply nat_compare_eq in Heqe1.
  intuition.
  simpl in H.
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
  lia.
(* Right subtree (greater) *)
+ case (compare n0 n) eqn:Heqe2.
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
+ case (compare n0 n) eqn:Heqe2.
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
induction t; simpl in H.
(* Base case *)
intuition.
(* Step case *)
case (compare n0 a) eqn:Heqe1 in H; simpl in H.
+ case (compare n0 n) eqn:Heqe2 in H.
  right.
  apply nat_compare_eq in Heqe1.
  apply nat_compare_eq in Heqe2.
  lia.
  left.
  simpl.
  trivial.
  left.
  simpl.
  trivial.
+ case (compare n0 n) eqn:Heqe2 in H.
  * left.
    simpl.
    apply nat_compare_eq in Heqe2.
    left.
    trivial.
  * intuition.
    apply nat_compare_lt in Heqe2.
    intuition.
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
  * left.
    simpl.
    intuition.
    apply nat_compare_lt in Heqe1.
    apply nat_compare_gt in Heqe2.
    intuition.
+ case (compare n0 n) eqn:Heqe2 in H.
  * left.
    simpl.
    apply nat_compare_eq in Heqe2.
    left.
    trivial.
  * destruct H.
    apply nat_compare_lt in Heqe2.
    intuition.
    destruct H. destruct IHt1.
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
    intuition.
  * destruct H.
    apply nat_compare_gt in Heqe2.
    intuition.
    destruct H. destruct IHt1.
    apply H.
    left.
    simpl.
    right.
    intuition.
    intuition.
    left.
    simpl.
    intuition.
Qed.


Theorem sortPreservesBST : forall t : tree, bst (sort t).
intros.
induction t.
simpl.
auto.
unfold sort.
simpl.
apply insertBST.
induction (treeToList t1 ++ treeToList t2). 
unfold listToBST.
simpl.
auto.
simpl.
apply insertBST.
intuition.
Qed.


Theorem occursBSTFromList : forall n : nat, forall l : list nat, In n l <-> occurs n (listToBST l).
Proof.
intros.
unfold iff.
split; intros.
- (* => *)
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
- (* <= *)
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

(* All elements are preserved after transformation *)
Theorem BSTToListPreservation : forall l : list nat, forall n : nat, In n l <-> occurs n (listToBST l).
Proof.
intros.
unfold iff.
split; intros.
- (* => *)
induction l.
(* Base case *)
intuition.
(* Step case *)
simpl.
simpl in H.
apply insertPreservation.
intuition.
- (* <= *)
induction l.
(* Base case *)
intuition.
(* Step case *)
simpl.
simpl in H.
apply insertPreservation in H.
intuition.
Qed.

(* All elements are preserved after transformation *)
Theorem ListToBSTPreservation : forall t : tree, forall n : nat, occurs n t <-> In n (treeToList t).
Proof.
intros.
unfold iff.
split; intros.
- (* => *)
induction t.
(* Base case *)
intuition.
(* Step case *)
simpl.
simpl in H.
case (compare n0 n) eqn:Heqe1 in H.
apply nat_compare_eq in Heqe1.
left.
apply Heqe1.
right.
apply nat_compare_lt in Heqe1.
apply in_or_app.
destruct H.
lia.
intuition.
apply nat_compare_gt in Heqe1.
destruct H.
lia.
intuition.
- (* <= *)
induction t.
(* Base case *)
intuition.
(* Step case *)
simpl.
case (compare n0 n) eqn:Heqe1 in H.
apply nat_compare_eq in Heqe1.
left.
lia.
right.
simpl in H.
destruct H.
apply nat_compare_lt in Heqe1.
lia.
apply in_app_or in H.
intuition.
apply nat_compare_gt in Heqe1.
simpl in H.
destruct H.
lia.
apply in_app_or in H.
intuition.
Qed.


Theorem occursBST : forall n : nat, forall t : tree, occurs n t <-> occurs n (sort t).
Proof.
intros.
unfold iff.
split; intros.
- (* => *)
induction t.
(* Base case *)
simpl.
intuition.
(* Step case *)
unfold sort.
apply BSTToListPreservation.
apply ListToBSTPreservation.
apply H.
- (* <= *)
induction t.
(* Base case *)
simpl.
intuition.
(* Step case *)
unfold sort in H.
apply BSTToListPreservation in H.
apply ListToBSTPreservation in H.
apply H.
Qed.


(* Definitions for Part 2 *)

Function optMin (n : nat) (m : option nat) : nat :=
  match m with
  | None => n
  | Some k => (min n k)
  end.

Fixpoint treeMin (t : tree) : option nat :=
  match t with
  | leaf => None
  | node lt k rt => Some (optMin (optMin k (treeMin lt) ) (treeMin rt))
end.

Fixpoint leftmost (t : tree) : option nat :=
  match t with
  | leaf => None
  | node lt k rt => match lt with
      | leaf => Some k
      | node lt1 k1 rt1 => leftmost lt
  end
end.

Fixpoint search (n : nat) (t : tree) : Prop :=
  match t with
  | leaf => False
  | node lt k rt => match (compare n k) with 
      | Eq => True
      | Lt => search n lt
      | Gt => search n rt
  end
end.


(* Proofs for Part 2 *)

(* The optMin method returns one of its arguments *)
Theorem optMinLemma : forall a : nat, forall b : nat, forall r : nat, (optMin a (Some b)) = r -> r = a \/ r = b.
Proof.
intros.
simpl in H.
lia.
Qed.

Theorem trivialMinComp : forall a : nat, forall b : nat, min a b = a -> a <= b.
Proof.
intros.
lia.
Qed.

(* The minimal element belongs to the tree *)
Theorem minInTree : forall t : tree, forall m : nat, treeMin t = Some m -> occurs m t.
Proof.
intros.
induction t; simpl in H.
- (* Base case *)
simpl. discriminate.
- (* Step case *)
case_eq (treeMin t1).
intros n1 Ht1.
rewrite Ht1 in H.
case_eq (treeMin t2).
intros n2 Ht2.
rewrite Ht2 in H.
simpl in H.
inversion H. rewrite -> H1.
apply optMinLemma in H1.
destruct H1; simpl.
  apply eq_sym in H0.
  apply optMinLemma in H0.
  destruct H0.
  lia.
  apply eq_sym in H0.
  rewrite H0 in Ht1.
  apply IHt1 in Ht1.
  right. left. apply Ht1.
  apply eq_sym in H0.
  rewrite H0 in Ht2.
  apply IHt2 in Ht2.
  right. right. apply Ht2.
intros.
rewrite H0 in H.
inversion H. rewrite -> H2.
apply optMinLemma in H2.
destruct H2; simpl.
  apply eq_sym in H1.
  lia.
  apply eq_sym in H1.
  rewrite H1 in Ht1.
  apply IHt1 in Ht1.
  right. left. apply Ht1.

intros.
rewrite H0 in H.
inversion H. rewrite H2.
case_eq (treeMin t2).
intros n2 Ht2.
rewrite Ht2 in H.
rewrite Ht2 in H2.
apply optMinLemma in H2.
destruct H2; simpl.
  lia.
  apply eq_sym in H1.
  rewrite H1 in Ht2.
  apply IHt2 in Ht2.
  right. right. apply Ht2.
intros.
rewrite H1 in H2.
firstorder.
Qed.

(* Theorems needed to place the subtrees in relation to a key *)
Theorem allRTGrtKey : forall n : nat, forall t : tree, (grtTree t n) -> (forall k, occurs k t -> k > n).
Proof.
intros.
induction t.
- (* Step case *)
simpl in H0.
lia.
- (* Base case *)
simpl in H.
destruct H. destruct H1.
simpl in H0.
destruct (compare n0 k) eqn:Heqe2 in H0.
  + intuition.
  + intuition.
  + intuition.
Qed.

Theorem allLTLessKey : forall n : nat, forall t : tree, (lessTree t n) -> (forall k, occurs k t -> k < n).
Proof.
intros.
induction t.
- (* Step case *)
simpl in H0.
lia.
- (* Base case *)
simpl in H.
destruct H. destruct H1.
simpl in H0.
destruct (compare n0 k) eqn:Heqe2 in H0.
  + intuition.
  + intuition.
  + intuition.
Qed.


(* The values in all nodes are geq than the minimal value *)
Theorem allNodesGeqMin : forall t : tree, forall m : nat, forall n : nat, treeMin t = Some m /\ occurs n t -> n >= m.
Proof.
intros.
intuition.
induction t; simpl in H1.
- (* Base case *)
lia.
- (* Step case *)
destruct H1.

rewrite H in H0.
simpl in H0.
case_eq (treeMin t1).
intros n1 Ht1.
rewrite Ht1 in H0.
case_eq (treeMin t2).
intros n2 Ht2.
rewrite Ht2 in H0.
simpl in H0.
inversion H0. rewrite -> H2.
apply optMinLemma in H2.
destruct H2.
  apply eq_sym in H1.
  rewrite H1 in H0.
  intuition.
  apply eq_sym in H1.
  rewrite H1 in Ht2.
  apply IHt2 in Ht2.
  lia.
  intuition.
Admitted.




(* Minimal element of BST is its leftmost node *)
Theorem minBSTLeftmost : forall t : tree, bst t -> treeMin t = leftmost t.
Proof.
intros.
induction t.
- (* Base case *)
intuition.
- (* Step case *)
assert (bst (node t1 n t2)).
assumption.
simpl in H.
destruct H.
destruct H1.
destruct H2.
assert (forall k, occurs k t1 -> k < n).
apply allLTLessKey.
intuition.
assert (forall k, occurs k t2 -> k > n).
apply allRTGrtKey.
intuition.
case_eq (treeMin (node t1 n t2)).
+ intros.
  case_eq (treeMin t1).
  * intros.
    case_eq (treeMin t2).
      intros.
      inversion H6.
      rewrite H10.
      rewrite H7 in H10.
      rewrite H8 in H10.
      apply optMinLemma in H10.
      destruct H10.
        simpl in H9.
        intuition.
        apply minInTree in H7.
        apply H4 in H7.
Admitted.

(* Search function is correct *)
Theorem searchCorrect : forall t : tree, forall n : nat, bst t -> (occurs n t <-> search n t).
Proof.
intros.
unfold iff.
split; intros.
- (* => *)
induction t.
(* Base case *)
intuition.
simpl.
destruct (compare n n0) eqn:Heqe1.
intuition.
simpl in H0.
apply nat_compare_lt in Heqe1.
intuition.
  + lia.
  + simpl in H.
    destruct H. destruct H1. destruct H2.
    apply IHt1 in H. apply H. apply H0.
  + simpl in H.
    destruct H. destruct H1. destruct H2.
    assert (forall k, occurs k t2 -> k > n0).
    apply allRTGrtKey.
    apply H3.
    assert (occurs n t2 -> n > n0).
    apply H4.
    apply H5 in H0.
    lia.
  + simpl in H0.
    apply nat_compare_gt in Heqe1.
    intuition.
    lia.
    intuition.
    simpl in H.
    destruct H. destruct H1. destruct H2.
    apply IHt2. apply H1.
    assert (forall k, occurs k t1 -> k < n0).
    apply allLTLessKey.
    apply H2.
    assert (occurs n t1 -> n < n0).
    apply H4.
    apply H5 in H0.
    lia.
    destruct H.
    intuition.
- (* <= *)
induction t.
(* Base case *)
intuition.
(* Step case *)
simpl.
destruct (compare n n0) eqn:Heqe1.
  + apply nat_compare_eq in Heqe1. intuition.
  + right.
    simpl in H.
    destruct H. destruct H1. destruct H2.
    intuition.
    simpl in H0.
    rewrite Heqe1 in H0.
    apply H4 in H0.
    intuition.
  + right.
    simpl in H.
    destruct H. destruct H1. destruct H2.
    intuition.
    simpl in H0.
    rewrite Heqe1 in H0.
    apply H5 in H0.
    intuition.
Qed.