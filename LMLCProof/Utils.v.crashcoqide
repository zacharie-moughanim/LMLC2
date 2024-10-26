Require Import PeanoNat.

Fixpoint find_opt {X : Type} (l : list X) (n : nat) : option X := match n with
  | 0 => match l with
    | nil => None
    | cons hd tl => Some hd
  end
  | S n' => match l with
    | nil => None
    | cons hd tl => find_opt tl n'
  end
end.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "l ++ l'" := (app l l') (at level 60, right associativity).

Lemma length_app : forall {X : Type} (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof. intros X l1 l2. induction l1.
  - reflexivity.
  - simpl. rewrite IHl1. reflexivity.
Qed.

Lemma minus_n_0 : forall (n : nat), n-0 = n.
Proof. destruct n as [|n'].
  - reflexivity.
  - reflexivity.
Qed.

Lemma minus_n_n : forall (n : nat), n-n = 0.
Proof. induction n as [|n' IHn].
  - reflexivity.
  - simpl. apply IHn.
Qed.

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof. intros n m. induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof. intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma minus_n_Sm_p : forall n m p : nat,
  n - S m - p = n - m - S p.
Proof.
  intros n. induction n.
  - reflexivity.
  - simpl. intros m p. destruct m.
    + simpl. rewrite minus_n_0. reflexivity.
    + apply IHn.
Qed.

Lemma plus_minus_assoc1 : forall n m p : nat,
  n - m - p = n - p - m.
Proof. intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. intros m p. destruct m.
    + simpl. destruct p.
      * reflexivity.
      * rewrite minus_n_0. reflexivity.
    + destruct p.
      * rewrite minus_n_0. simpl. reflexivity.
      * rewrite IHn'. apply minus_n_Sm_p.
Qed.


Example test_plus_minus : forall (a b c : nat), a + b - c - a = b - c.
Proof. 
  intros a. induction a.
  - simpl. intros b c. rewrite minus_n_0. reflexivity.
  - simpl. destruct c.
    + simpl. assert (H : a + b - 0 - a = b - 0). {apply IHa. } rewrite minus_n_0 in H. apply H.
    + rewrite <- minus_n_Sm_p.  apply IHa.
Qed.


Lemma find_opt_S : forall {X : Type} (l : list X) (n : nat), find_opt l (S n) <> None -> find_opt l n <> None.
Proof. Admitted.

Lemma find_opt_app1 : forall {X : Type} (l1 l2 : list X) (n : nat),
  find_opt l1 n <> None -> find_opt (l1++l2) n = find_opt l1 n.
Proof. intros *. generalize dependent n. induction l1 as [|h t IHt].
    + intro n. intro H. simpl in H. unfold not in H. destruct n.
      * exfalso. apply H. reflexivity.
      * exfalso. apply H. reflexivity.
    + destruct n as [|n'].
      * simpl. reflexivity.
      * simpl. intro H. apply IHt in H. apply H.
Qed.

Lemma find_opt_app2 : forall {X : Type} (l1 l2 : list X) (n : nat),
  find_opt l1 n =  None -> find_opt (l1++l2) n = find_opt l2 (n-(length l1)).
Proof. intros *. generalize dependent n. induction l1 as [|h t IHt].
    + simpl. intros n H. rewrite minus_n_0. reflexivity.
    + intros n H. simpl in H. destruct n.
      * discriminate H.
      * apply IHt in H. simpl. apply H.
Qed.

Lemma find_opt_length_bound : forall {X : Type} (n : nat) (l : list X),
      find_opt l n <> None -> find_opt l (S n) = None -> length l = S n.
Proof. intro X. induction n as [|n' IHn].
  - intros * H G. destruct l as [|h t ].
    + simpl in H. exfalso. apply H. reflexivity.
    + simpl. simpl in H. simpl in G. induction t as [|ht tt].
      * reflexivity.
      * simpl in G. discriminate G.
  - intros * H G. destruct l as [|h t].
    + simpl in H. exfalso. apply H. reflexivity.
    + simpl in H. simpl in G. apply IHn in H.
      * simpl. rewrite H. reflexivity.
      * apply G.
Qed.

Lemma no_positive_less_than_zero : forall (n : nat), S n <= 0 -> False.
Proof. intros n H. inversion H. Qed.

Lemma Succ_n_minus_1 : forall (n : nat), 1 <= n -> S(n-1) = n.
Proof.
  intros n H.
  destruct n.
  - apply no_positive_less_than_zero in H. contradiction.
  - simpl. rewrite minus_n_0. reflexivity.
Qed.

Lemma find_opt_length : forall {X : Type} (l : list X) (n : nat), length l <= n -> find_opt l n = None.
Proof. intro X. induction l as [|h t IHt].
  - intros n H. simpl. destruct n. all : reflexivity.
  - intros n H. simpl in H. simpl. destruct n as [|n'].
    + apply no_positive_less_than_zero in H. exfalso. apply H.
    + apply le_S_n in H. apply IHt in H. apply H.
Qed.

Lemma all_positive_more_than_zero : forall (n : nat), 0 <= n.
Proof. induction n as [|n' IH].
  - trivial.
  - apply le_S. apply IH.
Qed.

Search (S _ <= S _).

Lemma find_opt_length_2 : forall {X : Type} (l : list X) (n : nat), find_opt l n <> None -> n <= length l.
Proof. 
  intros X l.
  induction l as [|h tl IHtl].
  - intros n H. destruct n.
    + contradiction.
    + contradiction.
  - simpl. intros n. destruct n.
    + intros H. apply all_positive_more_than_zero.
    + intros H. apply IHtl in H. apply le_n_S. apply H.
Qed.

Lemma find_opt_length_2' : forall {X : Type} (l : list X) (n : nat), find_opt l n = None -> length l <= n.
Proof. 
  intros X l.
  induction l as [|h tl IHtl].
  - intros n H. destruct n.
    + simpl. reflexivity.
    + simpl. apply all_positive_more_than_zero.
  - simpl. intros n. destruct n.
    + intros H. discriminate H.
    + intros H. apply IHtl in H. apply le_n_S. apply H.
Qed.

Definition tail {X : Type} (lst : list X) := match lst with
  | h::t => t
  | nil => nil
end.

Fixpoint remove_nat (lst : list nat) (x : nat) : list nat := match lst with
  | nil => nil
  | h::t => if x =? h then remove_nat t x else h :: (remove_nat t x)
end.

Fixpoint in_list (lst : list nat) (x : nat) : bool := match lst with
  | nil => false
  | h::t => if x =? h then true else (in_list t x)
end.

Lemma in_list_app1 : forall (l1 l2 : list nat) (x : nat), in_list (l1 ++ l2) x = false ->
                                          in_list l1 x = false /\ in_list l2 x = false.
Proof. intros *. intro H. induction l1 as [|h t IHt1].
  - simpl. split.
    + reflexivity.
    + simpl in H. apply H.
  - simpl. destruct (x =? h) eqn:eqxh.
    + simpl in H. rewrite eqxh in H. discriminate H.
    + simpl in H. rewrite eqxh in H. apply IHt1 in H. apply H.
Qed.

Lemma in_list_app2 : forall (l1 l2 : list nat) (x : nat), in_list (l1 ++ l2) x = true ->
                                          in_list l1 x = true \/ in_list l2 x = true. 
Proof. intros *. intro H. induction l1 as [| h t IHt1].
  - simpl. right. apply H.
  - simpl. simpl in H. destruct (x =? h).
    + left. reflexivity.
    + apply IHt1 in H. apply H.
Qed.

Lemma eqb_to_eq : forall (x y : nat), x =? y = true -> x = y.
Proof. induction x as[|x' IHx].
  - intro y. destruct y as [|y'].
    + reflexivity.
    + simpl. discriminate.
  - intro y. destruct y as [|y'].
    + simpl. discriminate.
    + simpl. intro H. apply IHx in H. rewrite H. reflexivity.
Qed.

Lemma leb_to_ltb : forall (n m : nat), n <=? m = false -> m <? n = true.
Proof. induction n as [|n' IHn].
  - intros m H. simpl in H. discriminate H.
  - intros m H. destruct m as [|m'].
    + unfold Nat.ltb. unfold Nat.leb. reflexivity.
    + simpl in H. apply IHn in H. apply H.
Qed.

Lemma in_remove_nat_neq : forall (l : list nat) (x y : nat), (x =? y = false) ->
            in_list (remove_nat l x) y = in_list l y.
Proof. intros *. intros H. induction l as [|h t IHt].
  - reflexivity.
  - simpl. destruct (x =? h) eqn:eqxh.
    + destruct (y =? h) eqn:eqyh.
      * apply eqb_to_eq in eqxh. apply eqb_to_eq in eqyh. rewrite eqxh in H. rewrite eqyh in H.
        rewrite Nat.eqb_refl in H. discriminate H.
      * apply IHt.
    + destruct (y =? h) eqn:eqyh.
      * simpl. rewrite eqyh. reflexivity.
      * simpl. rewrite eqyh. apply IHt.
Qed.



