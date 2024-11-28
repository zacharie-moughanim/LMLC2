Require Import PeanoNat.
From Coq Require Import Lists.List.

Fixpoint find_opt {X : Type} (l : list X) (n : nat) : option X :=
  match n with
  | 0 =>
    match l with
    | nil => None
    | cons hd tl => Some hd
    end
  | S n' =>
    match l with
    | nil => None
    | cons hd tl => find_opt tl n'
    end
end.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "l ++ l'" := (app l l') (at level 60, right associativity).

Lemma length_app:
  forall {X : Type} (l1 l2 : list X), length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1; simpl; auto.
Qed.

Lemma minus_n_0:
  forall (n : nat), n - 0 = n.
Proof.
  now destruct n as [|n'].
Qed.

Lemma minus_n_n :
  forall (n : nat), n - n = 0.
Proof.
  now induction n.
Qed.

Lemma plus_comm:
  forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn']; simpl.
  - now rewrite <- plus_n_O.
  - now rewrite IHn', plus_n_Sm.
Qed.

Lemma plus_assoc:
  forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn']; simpl; auto.
Qed.

Lemma minus_n_Sm_p:
  forall n m p : nat, n - S m - p = n - m - S p.
Proof.
  intros n. induction n; simpl; auto.
  intros [] p; simpl; auto.
  now rewrite minus_n_0.
Qed.

Lemma plus_minus_assoc1:
  forall n m p : nat, n - m - p = n - p - m.
Proof.
  intros n.
  induction n as [|n' IHn']; simpl; auto.
  intros [] []; simpl; auto.
  + now rewrite minus_n_0.
  + now rewrite minus_n_0.
  + now rewrite IHn', minus_n_Sm_p.
Qed.

Example test_plus_minus:
  forall (a b c : nat), a + b - c - a = b - c.
Proof.
  intros a. induction a; simpl.
  - intros b c.
    now rewrite minus_n_0.
  - intros b []; simpl; auto.
    + assert (H : a + b - 0 - a = b - 0) by apply IHa. 
      now rewrite minus_n_0 in H.
    + now rewrite <- minus_n_Sm_p.
Qed.

Lemma find_opt_app1:
  forall {X : Type} (l1 l2 : list X) (n : nat),
    find_opt l1 n <> None -> find_opt (l1++l2) n = find_opt l1 n.
Proof.
  intros *. revert n.
  induction l1 as [|h t IHt].
  + now intros [] H; simpl in *.
  + destruct n as [|n']; simpl; auto.
Qed.

Lemma find_opt_app2:
  forall {X : Type} (l1 l2 : list X) (n : nat),
    find_opt l1 n = None -> find_opt (l1++l2) n = find_opt l2 (n-(length l1)).
Proof.
  intros *. revert n.
  induction l1 as [|h t IHt]; simpl.
  + intros n H. now rewrite minus_n_0.
  + intros [] H; simpl in *; try easy.
    now apply IHt.
Qed.

Lemma find_opt_length_bound:
  forall {X : Type} (n : nat) (l : list X),
    find_opt l n <> None -> find_opt l (S n) = None -> length l = S n.
Proof.
  intro X. induction n as [|n' IHn].
  - intros * H G. destruct l as [|h t ]; simpl in *; try easy.
    now induction t as [ | ht tt ]; simpl in *; auto.
  - intros * H G.
    now destruct l as [|h t]; simpl in *; auto.
Qed.

Lemma no_positive_less_than_zero:
  forall (n : nat), S n <= 0 -> False.
Proof.
  easy.
Qed.

Lemma Succ_n_minus_1:
  forall (n : nat), 1 <= n -> S(n-1) = n.
Proof.
  intros [] H; simpl.
  - now apply no_positive_less_than_zero in H.
  - now rewrite minus_n_0.
Qed.

Lemma find_opt_length:
  forall {X : Type} (l : list X) (n : nat), length l <= n -> find_opt l n = None.
Proof.
  intro X. induction l as [|h t IHt].
  - now intros [] H.
  - intros [] H; simpl in *.
    + now apply no_positive_less_than_zero in H.
    + apply le_S_n in H. auto.
Qed.

Lemma all_positive_more_than_zero:
  forall (n : nat), 0 <= n.
Proof.
  induction n as [|n' IH]; auto.
Qed.

Lemma find_opt_length_2''':
  forall {X : Type} (l : list X) (n : nat), find_opt l n <> None -> n < length l.
Proof. 
  intros X l.
  induction l as [|h tl IHtl]; simpl in *.
  - now intros [] H.
  - intros [] H.
    + apply Nat.lt_0_succ.
    + apply IHtl in H.
      apply le_n_S.
      apply H.
Qed.

Lemma find_opt_length_2'':
  forall {X : Type} (l : list X) (n : nat), find_opt l n <> None -> n <= length l.
Proof.
  intros.
  apply Nat.lt_le_incl.
  apply find_opt_length_2'''.
  apply H.
Qed.

Lemma find_opt_length_3 :
  forall {X : Type} (l : list X) (n : nat), n < length l -> find_opt l n <> None.
Proof.
  intros. revert n H.
  induction l as [|h t]; simpl in *; try easy.
  intros [] H; simpl in *; try easy.
  apply IHt.
  now apply PeanoNat.lt_S_n.
Qed.

Lemma find_opt_S:
  forall {X : Type} (l : list X) (n : nat), find_opt l (S n) <> None -> find_opt l n <> None.
Proof.
  intros. apply find_opt_length_2'' in H.
  apply find_opt_length_3.
  unfold lt. apply H.
Qed.

Lemma find_opt_length_2':
  forall {X : Type} (l : list X) (n : nat), find_opt l n = None -> length l <= n.
Proof. 
  intros X l.
  induction l as [|h tl IHtl]; simpl.
  - intros [] H; simpl; try easy.
    apply all_positive_more_than_zero.
  - intros [] H; try easy.
    apply IHtl in H.
    apply le_n_S.
    apply H.
Qed.

Definition tail {X : Type} (lst : list X) :=
  match lst with
  | h::t => t
  | nil => nil
end.

Fixpoint remove_nat (lst : list nat) (x : nat) : list nat :=
  match lst with
  | nil => nil
  | h::t => if x =? h then remove_nat t x else h :: (remove_nat t x)
end.

Fixpoint in_list (lst : list nat) (x : nat) : bool :=
  match lst with
  | nil => false
  | h::t => if x =? h then true else (in_list t x)
end.

Lemma in_list_app1:
  forall (l1 l2 : list nat) (x : nat),
    in_list (l1 ++ l2) x = false ->
    in_list l1 x = false /\ in_list l2 x = false.
Proof.
  intros * H.
  induction l1 as [|h t IHt1]; simpl; auto.
  destruct (x =? h) eqn:eqxh; simpl in *.
  + now rewrite eqxh in H.
  + rewrite eqxh in H.
    apply IHt1 in H.
    apply H.
Qed.

Lemma in_list_app2:
  forall (l1 l2 : list nat) (x : nat),
    in_list (l1 ++ l2) x = true ->
    in_list l1 x = true \/ in_list l2 x = true. 
Proof.
  intros * H.
  induction l1 as [| h t IHt1]; simpl in *.
  - now right.
  - destruct (x =? h); auto.
Qed.

Lemma eqb_to_eq :
  forall (x y : nat), x =? y = true -> x = y.
Proof.
  induction x as[|x' IHx].
  - now intros [].
  - now intros []; simpl; auto.
Qed.

Lemma leb_to_ltb:
  forall (n m : nat), n <=? m = false -> m <? n = true.
Proof.
  induction n as [|n' IHn]; simpl in *; try easy.
  intros [] H; simpl in *; try easy.
  now apply IHn.
Qed.

Lemma in_remove_nat_neq:
  forall (l : list nat) (x y : nat),
    (x =? y = false) ->
    in_list (remove_nat l x) y = in_list l y.
Proof.
  intros * H.
  induction l as [|h t IHt]; simpl in *; auto.
  destruct (x =? h) eqn:eqxh, (y =? h) eqn:eqyh; simpl.
  - apply eqb_to_eq in eqxh.
    apply eqb_to_eq in eqyh.
    now rewrite eqxh, eqyh, Nat.eqb_refl in H.
  - apply IHt.
  - now rewrite eqyh.
  - now rewrite eqyh.
Qed.

Lemma in_list_app3:
  forall (x : nat) (l1 l2 : list nat), in_list l1 x = true -> in_list (l1++l2) x = true.
Proof.
  induction l1 as [|h1 t1]; simpl; try easy.
  intros. destruct (x =? h1); auto.
Qed.

Lemma in_list_neq:
  forall (x y : nat) (l1 l2 : list nat), in_list (l1++y::l2) x = true -> x <> y -> in_list (l1++l2) x = true.
Proof.
  intros. induction l1 as [|h1 t1]; simpl in *.
  - apply Nat.eqb_neq in H0.
    now rewrite H0 in H.
  - destruct (x =? h1); auto.
Qed.

Lemma in_list_app_comm:
  forall (x : nat) (l1 l2 : list nat), in_list (l1++l2) x = true <-> in_list (l2++l1) x = true.
Proof.
  assert (one_dir : forall (x : nat) (l1 l2 : list nat), in_list (l1++l2) x = true -> in_list (l2++l1) x = true). {
    intros * H. revert l1 H.
    induction l2 as [|h2 t2 IHt2]; intros l1 H.
    - now rewrite app_nil_r in H.
    - simpl. destruct (x =? h2) eqn:eqxh2; auto.
    apply IHt2.
    apply in_list_neq with (y := h2); auto.
    now apply Nat.eqb_neq.
  }
  firstorder.
Qed.

Lemma not_in_neq:
  forall (x : nat) (l : list nat),
    in_list l x = false <-> (forall y, in_list l y = true -> y <> x).
Proof.
  intros. split.
  - intro H.
    induction l as [|h t]; try easy.
    intros; simpl in *.
    destruct (y =? h) eqn:eqyh.
    + apply Nat.eqb_eq in eqyh.
      intro G. rewrite <- G in H.
      rewrite eqyh in H. simpl in H.
      now rewrite Nat.eqb_refl in H.
    + apply Nat.eqb_neq in eqyh.
      destruct (x =? h) eqn:eqxh; try easy.
      apply Nat.eqb_neq in eqxh.
      auto.
  - intro H. induction l as [|h t]; simpl; auto.
    destruct (x =? h) eqn:eqxh.
    + apply Nat.eqb_eq in eqxh.
      exfalso. symmetry in eqxh.
      eapply H; simpl.
      now rewrite Nat.eqb_refl.
      auto.
    + apply IHt. intros y Hy.
      apply H. simpl.
      now destruct (y =? h).
Qed.

Lemma in_list_remove:
  forall (x y : nat) (l : list nat),
    in_list (remove_nat l y) x = false ->
    x <> y -> in_list l x = false.
Proof.
  intros. induction l as [|h t IHt]; simpl in *; auto.
  destruct (y =? h) eqn:eqyh.
  + apply Nat.eqb_eq in eqyh.
    rewrite <- eqyh.
    apply Nat.eqb_neq in H0.
    rewrite H0.
    apply IHt, H.
  + destruct (x =? h) eqn:eqxh; simpl in *.
    - now rewrite eqxh in H.
    - apply IHt. now rewrite eqxh in H.
Qed.