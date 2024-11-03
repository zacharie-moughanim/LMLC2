From Coq Require Import Lists.List.
Require Import PeanoNat.
Import ListNotations.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Definitions.

From LMLCProof Require Import Utils Source.

Inductive lambda_term : Type :=
  | Lvar (x : var)
  | Lappl (f : lambda_term) (arg : lambda_term)
  | Labs (x : var) (M : lambda_term).

(* capture-avoiding substitution *)
Fixpoint substitution (M N : lambda_term) (x : var) : lambda_term := match M with
  | Lvar y => if x =? y then N else Lvar y
  | Labs y M' => if x =? y then Labs y M' else Labs y (substitution M' N x)
  | Lappl M' N' => Lappl (substitution M' N x) (substitution N' N x)
end.

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
  | contextual_lambda : forall (x : var) (M N : lambda_term), beta_reduction M N -> beta_reduction (Labs x M) (Labs x N)
  | contextual_function : forall (M N M' : lambda_term), beta_reduction M M' -> beta_reduction (Lappl M N) (Lappl M' N)
  | contextual_argument : forall (M N N' : lambda_term), beta_reduction N N' -> beta_reduction (Lappl M N) (Lappl M N')
  | redex_contraction : forall (x : var) (M N : lambda_term), beta_reduction (Lappl (Labs x M) N) (substitution M N x)
.

Inductive refl_trans_closure {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | refl : forall (x : X), refl_trans_closure R x x
  | trans : forall (x y z: X), refl_trans_closure R x y -> refl_trans_closure R y z -> refl_trans_closure R x z
  | onestep : forall (x y : X), R x y -> refl_trans_closure R x y
.

Definition beta_star := refl_trans_closure beta_reduction.
Definition ml_red_star := refl_trans_closure ml_reduction.
Notation "M ->b N" := (beta_reduction M N) (at level 50).
Notation "M ->ml N" := (ml_reduction M N) (at level 50).

Notation "M ->b* N" := (beta_star M N) (at level 50).
Notation "M ->ml* N" := (ml_red_star M N) (at level 50).
Notation "M [ N / x ]" := (substitution M N x) (at level 40).
Notation "M ml[ N / x ]" := (ml_substitution M N x) (at level 40).

Lemma bredstar_cont_subst : forall (x : var) (M M' N N' : lambda_term), M ->b* M' -> N ->b* N' -> substitution M N x ->b* substitution M' N' x.
Proof. Admitted. (*not sure if that will be useful*)
(* fresh variables *)

Fixpoint fvL (M : lambda_term) : list var := match M with
  | Lvar x => [x]
  | Labs x M' => remove_nat (fvL M') x
  | Lappl M' N' => (fvL M') ++ (fvL N')
end.

Inductive alpha_equivalence : lambda_term -> lambda_term -> Prop :=
  | alpha_context_var : forall (x : var), alpha_equivalence (Lvar x) (Lvar x)
  | alpha_context_labs : forall (M : lambda_term) (N : lambda_term) (x:var), alpha_equivalence M N -> alpha_equivalence (Labs x M) (Labs x N)
  | alpha_context_appl : forall (M : lambda_term) (N : lambda_term) (M' : lambda_term) (N' : lambda_term),
                                alpha_equivalence M M' -> alpha_equivalence N N' ->
                                                              alpha_equivalence (Lappl M N) (Lappl M' N')
  | alpha_rename : forall (M N new_N : lambda_term) (x new_x:var), ~(In new_x (fvL N)) -> alpha_equivalence M N ->
                          new_N = substitution N (Lvar new_x) x  -> alpha_equivalence (Labs x M) (Labs new_x new_N).

Notation "M ~a N" := (alpha_equivalence M N) (at level 50).

Lemma alpha_refl : forall (M : lambda_term), M ~a M.
Proof. induction M.
  - apply alpha_context_var.
  - apply alpha_context_appl. apply IHM1. apply IHM2.
  - apply alpha_context_labs. apply IHM.
Qed.

Lemma alpha_sym : forall (M N : lambda_term), M ~a N -> N ~a M.
Proof. Admitted. (*not sure if that will be useful*)

Axiom alpha_quot : forall (M N : lambda_term), M ~a N -> M = N.

Lemma alpha_eq : forall (M N : lambda_term), M = N -> M ~a N.
Proof. Admitted.

Lemma fresh_of_fresh_is_fresh : forall (x : nat) (l : list nat), x = fresh l -> in_list l (fresh [x]) = false.
Proof. assert (forall l  y,  in_list l y = true -> y < (fresh l)). { intros l y G. unfold fresh. apply fresh_aux_spec2. apply G. }
       assert (forall l x y, in_list l y = true -> fresh l <= x -> y < x). { intros. apply Lt.lt_le_trans with (m := fresh l). apply H. apply H0. apply H1. }
       clear H. intros x l G. apply not_in_neq. intros. apply Nat.lt_neq. apply (H0 l).
       apply H. rewrite <- G. apply Nat.lt_le_incl. apply (H0 [x]). simpl. rewrite Nat.eqb_refl. reflexivity.
       apply Le.le_refl.
Qed.

Lemma fresh_spec_2 : forall (l : list nat), in_list l (fresh l) = false.
Proof. intros. destruct (in_list l (fresh l)) eqn:eq.
  - unfold fresh in eq. apply fresh_aux_spec2 with (n := 0) in eq.
    exfalso. apply Nat.lt_irrefl in eq. apply eq.
  - reflexivity.
Qed.

(* Basic terms constructors *)

(* Boolean *)
Definition church_true := Labs 0 (Labs 1 (Lvar 0)).
Definition church_false := Labs 0 (Labs 1 (Lvar 1)).
Definition church_if (c t e : lambda_term) := Lappl (Lappl c t) e.
Definition church_and (b1 b2 : lambda_term) := church_if b1 b2 church_false.
Definition church_or (b1 b2 : lambda_term) := church_if b1 church_true b2.

(* Pairs *)

Definition church_pair (M : lambda_term) (N : lambda_term) : lambda_term :=
  let x := fresh ((fvL M) ++ (fvL N)) in
  Labs x (Lappl (Lappl (Lvar x) M) N).
Definition church_fst (P : lambda_term) : lambda_term := Lappl P (Labs 0 (Labs 1 (Lvar 0))).
Definition church_snd (P : lambda_term) : lambda_term := Lappl P (Labs 0 (Labs 1 (Lvar 1))).

(* Integer *)
Fixpoint church_int_free (n : nat) : lambda_term := match n with
  | 0 => Lvar 0
  | S n' => Lappl (Lvar 1) (church_int_free n')
end.
Definition church_int (n : nat) : lambda_term := Labs 1 (Labs 0 (church_int_free n)).
Definition church_succ (N : lambda_term) : lambda_term :=
    Labs 2 (Labs 0 (Labs 1 (
            (Lappl (Lvar 2)
                  (Lappl (Lappl (Lvar 2)
                              (Lvar 0))
                  (Lvar 1))
            )
           ))).
Definition church_succ2 (N : lambda_term) : lambda_term :=
  match N with
  | Lvar _ => N
  | Lappl _ _ => N
  | Labs f N' => (match N' with
                  | Lvar _ => N
                  | Lappl _ _ => N
                  | Labs x N'' => Labs f (Labs x (Lappl (Lvar f) N''))
                  end)
end.

Definition church_pred (N : lambda_term) : lambda_term :=
  church_snd
  (Lappl (Lappl N
            (Labs 0 (Labs 1
                          (Lappl (Lappl (Lvar 1) (church_succ2 (church_snd (Lvar 0))))
                               (church_succ (church_snd (Lvar 0)))))))
       (church_pair (church_int 0) (church_int 0))).

Definition church_plus (M N : lambda_term) (s z : var) : lambda_term :=
                               Labs s (Labs z (
                                                 Lappl (Lappl N (Lvar s))
                                                       (Lappl (Lappl M (Lvar s))
                                                              (Lvar z)))
                                              ).
Definition church_minus (M N : lambda_term) : lambda_term :=
      Lappl (Lappl M (Labs 0 (church_pred (Lvar 0)))) N.
Definition church_times (M N : lambda_term) : lambda_term :=
let x := fresh ((fvL M) ++ (fvL N)) in let y := fresh (x::((fvL M) ++ (fvL N))) in
                               Labs x (Labs y (
                                                 Lappl (Lappl N (Lvar x))
                                                       (Lappl (Lappl M (Lvar x))
                                                              (Lvar y)))
                                              ).
Definition church_gtz (M : lambda_term) : lambda_term := Lappl (Lappl M (Labs 0 church_true)) (church_false).

(* Turing fixpoint *)

Definition turing_fixpoint_half : lambda_term := 
                        Labs 1 (Labs 0 (Lappl (Lvar 0) (Lappl (Lappl (Lvar 1) (Lvar 1)) (Lvar 0)))).

Definition turing_fixpoint : lambda_term := Lappl turing_fixpoint_half turing_fixpoint_half.

Definition turing_fixpoint_applied (M : lambda_term) : lambda_term := Lappl M (Lappl (turing_fixpoint) M).

(** lemmas about constuctors *)

(** substitution lemmas *)
Lemma subst_lambda_cont : forall (M N : lambda_term) (x y : var), x <> y ->
                                    substitution (Labs x M) N y = Labs x (substitution M N y).
Proof. intros. simpl. apply Nat.eqb_neq in H. rewrite Nat.eqb_sym. rewrite H. reflexivity. Qed.

Lemma subst_appl_cont : forall (M N P : lambda_term) (x : var),
                                    substitution (Lappl M N) P x = Lappl (substitution M P x) (substitution N P x).
Proof. reflexivity. Qed.

(** beta-reduction properties *)

Lemma beta_red_is_transitive : transitive lambda_term (beta_star).
Proof. unfold transitive. intros *. unfold beta_star. apply trans. Qed.

Lemma bredstar_contextual_abs :
  forall (x : var) (M M': lambda_term), M ->b* M' -> Labs x M ->b* Labs x M'.
Proof. intros. induction H as [M'|M1 M2 M3 Red1 IHred1 Red2 IHred2|M N Honestep].
  - apply refl.
  - apply trans with (y := Labs x M2).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_lambda with (x := x) in Honestep. apply Honestep.
Qed.

Lemma bredstar_contextual_appl_function :
  forall (M M' N : lambda_term), M ->b* M' -> Lappl M N ->b* Lappl M' N.
Proof. intros *. intros red. induction red as [M'|M1 M2 M3 Red1 IHred1 Red2 IHred2|M M' Honestep].
  - apply refl.
  - apply trans with (y := Lappl M2 N).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_function. apply Honestep.
Qed.

Lemma bredstar_contextual_appl_argument :
  forall (M N N': lambda_term), N ->b* N' -> Lappl M N ->b* Lappl M N'.
Proof. intros *. intros red.  induction red as [N'|N1 N2 N3 Red1 IHred1 Red2 IHred2|N N' Honestep].
  - apply refl.
  - apply trans with (y := Lappl M N2).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_argument. apply Honestep.
Qed.

Lemma bredstar_contextual_appl :
  forall (M M' N N': lambda_term), M ->b* M' -> N ->b* N' -> Lappl M N ->b* Lappl M' N'.
Proof. intros *. intros redlhs redrhs. apply trans with (y := Lappl M' N).
  - apply bredstar_contextual_appl_function. apply redlhs.
  - apply bredstar_contextual_appl_argument. apply redrhs.
Qed.


Lemma substitution_fresh_l : forall (M N : lambda_term) (x : var), in_list (fvL M) x = false -> substitution M N x = M.
Proof. intros M P x H. induction M as [y | M IHM N IHN | y M IHM].
  - simpl. simpl in H. destruct (x =? y).
    + inversion H.
    + reflexivity.
  - simpl. simpl in H. apply in_list_app1 in H. destruct H as [H1 H2].
    rewrite IHM. rewrite IHN. reflexivity. apply H2. apply H1.
  - simpl. destruct (x =? y) eqn:eqxy.
    + reflexivity.
    + simpl in H. assert (cont : substitution M P x = M).
      * apply IHM. apply in_list_remove with (y := y). apply H. apply Nat.eqb_neq. apply eqxy.
      * rewrite cont. reflexivity.
Qed.


Lemma substitution_comm : forall (x y : var) (M N N' : lambda_term),
      x <> y -> in_list (fvL N) y = false -> in_list (fvL N') x = false ->
      substitution (substitution M N x) N' y = substitution (substitution M N' y) N x.
Proof. intros *. intros neqxy HN HN'. induction M as [z | Mfun IHfun Marg IHarg | z M' IHabs].
  - simpl. destruct (x =? z) eqn:eqxz.
    + destruct (y =? z) eqn:eqyz.
      * exfalso. apply neqxy. apply Nat.eqb_eq in eqxz. apply Nat.eqb_eq in eqyz.
        rewrite eqxz. rewrite eqyz. reflexivity.
      * intros. simpl. rewrite eqxz. rewrite substitution_fresh_l. reflexivity.
        apply HN.
    + destruct (y =? z) eqn:eqyz.
      * simpl. rewrite eqyz. rewrite substitution_fresh_l. reflexivity.
        apply HN'.
      * simpl. rewrite eqxz. rewrite eqyz. reflexivity.
  - simpl. rewrite IHfun. rewrite IHarg. reflexivity.
  - destruct (x =? z) eqn:eqxz.
    + destruct (y =? z) eqn:eqyz.
      * simpl. rewrite eqxz. rewrite eqyz. simpl. rewrite eqxz. rewrite eqyz. reflexivity.
      * simpl. rewrite eqxz. rewrite eqyz. simpl. rewrite eqxz. rewrite eqyz. reflexivity.
    + destruct (y =? z) eqn:eqyz.
      * simpl. rewrite eqxz. rewrite eqyz. simpl. rewrite eqxz. rewrite eqyz. reflexivity.
      * simpl. rewrite eqxz. rewrite eqyz. simpl. rewrite eqxz. rewrite eqyz. rewrite IHabs.
        reflexivity.
Qed.

Lemma church_plus_is_plus : forall (n m : nat) (s z : var),
      s <> 0 -> z <> 1 -> s <> z ->
      (substitution (substitution (church_int_free m) (Lvar s) 1)
      ((substitution (substitution (church_int_free n) (Lvar s) 1) (Lvar z) 0)) 0) ->b*
       substitution (substitution (church_int_free (n + m)) (Lvar z) 0) (Lvar s) 1.
Proof. intros. induction m as [|m' IHm'].
  - simpl. rewrite <- plus_n_O.
           assert (substitution (substitution (church_int_free n) (Lvar s) 1) (Lvar z) 0 =
                   substitution (substitution (church_int_free n) (Lvar z) 0) (Lvar s) 1).
    {
      apply substitution_comm.
      - intro contra. discriminate contra.
      - simpl. destruct s as [|s'].
        + exfalso. apply H. reflexivity.
        + reflexivity.
      - simpl. destruct z as [|z'].
        + reflexivity.
        + destruct z' as [|z''].
          * exfalso. apply H0. reflexivity.
          * reflexivity.
    }
    rewrite H2. apply refl.
  - simpl. destruct s as [|s'].
    + exfalso. apply H; reflexivity.
    + rewrite <- plus_n_Sm. remember (church_int_free n) as churchN.
      remember (church_int_free m') as churchM'. simpl. remember (church_int_free (n+m')) as churchNpM'.
      apply bredstar_contextual_appl.
      * apply refl.
      * apply IHm'.
Qed.

Lemma church_int_Sn : forall (n : nat), church_int_free (S n) = Lappl (Lvar 1) (church_int_free n).
Proof. reflexivity. Qed.

Lemma church_gtz_Sn : forall (n : nat),
      (substitution (substitution (church_int_free (S n)) (Labs 0 church_true) 1) church_false 0) ->b* church_true.
Proof. intro n. induction n as [|n'].
  - simpl. apply trans with (y := substitution church_true church_false 0).
    + apply onestep; apply redex_contraction.
    + simpl. unfold church_true. apply refl.
  - rewrite church_int_Sn. rewrite subst_appl_cont. rewrite subst_appl_cont.
    apply trans with (y := Lappl (substitution (substitution (Lvar 1) (Labs 0 church_true) 1) church_false 0)
                                  church_true).
    + apply bredstar_contextual_appl.
      * apply refl.
      * apply IHn'.
    + simpl. apply trans with (y := substitution church_true church_true 0).
      * apply onestep; apply redex_contraction.
      * simpl. apply refl.
Qed.