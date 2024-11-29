From Coq Require Import Lists.List.
Require Import PeanoNat Lia.
Import ListNotations.
Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Classes.RelationClasses.

From LMLCProof Require Import Utils.

(** * Simple Formalization of the Pure Lambda Calculus *)

Definition var : Type := nat.

(** Lambda Terms *)
Inductive term : Type :=
  | Lvar (x : var)
  | Lappl (f : term) (arg : term)
  | Labs (x : var) (M : term).

(** Decidable Equality *)
Lemma eq_dec:
  forall (e1 e2 : term), {e1 = e2} + {e1 <> e2}.
Proof.
  do 2 decide equality.
Defined.

Notation "M =? N" := (eq_dec M N).

(** Capture-avoiding substitution *)
Fixpoint substitution (M N : term) (x : var) : term :=
  match M with
  | Lvar y =>
    if Nat.eq_dec x y then N else Lvar y
  | Labs y M' =>
    if Nat.eq_dec x y then Labs y M' else Labs y (substitution M' N x)
  | Lappl M' N' =>
    Lappl (substitution M' N x) (substitution N' N x)
end.

(** ** Small-step, Right-to-left, Call-by-value Semantics *)

(** Values are irreducible terms (lambdas, and variables) *)
Inductive is_value : term -> Prop :=
  | Lvar_is_value x   : is_value (Lvar x)
  | Labs_is_value x e : is_value (Labs x e).

Inductive step_cbv : term -> term -> Prop :=
  | step_Lappl_r e1 e2 e2':
    step_cbv e2 e2' ->
    step_cbv (Lappl e1 e2) (Lappl e1 e2')

  | step_Lappl_l e1 e1' e2:
    is_value e2 ->
    step_cbv e1 e1' ->
    step_cbv (Lappl e1 e2) (Lappl e1' e2)

  | step_beta x e1 e2 :
    is_value e2 ->
    step_cbv (Lappl (Labs x e1) e2) (substitution e1 e2 x).

(** ** Big-step, Right-to-left, Call-by-value Semantics *)
Inductive eval_cbv : term -> term -> Prop :=
  | eval_value e:
    is_value e -> eval_cbv e e

  | eval_Lapp e1 x e1' e2 e2' v:
    eval_cbv e1 (Labs x e1') ->
    eval_cbv e2 e2' ->
    eval_cbv (substitution e1' e2' x) v ->
    eval_cbv (Lappl e1 e2) v.

(** The big-step semantics always produces irreducible terms (values) *)
Theorem eval_to_value:
  forall e v, eval_cbv e v -> is_value v.
Proof.
  induction 1; auto.
Qed.

Definition steps := clos_refl_trans_1n _ step_cbv.

Instance steps_refl:
  Reflexive steps.
Proof.
  intros x. apply rt1n_refl.
Qed.

Instance steps_trans:
  Transitive steps.
Proof.
  intros x y z Hxy Hyz.
  induction Hxy as [ | x y y' Hy'z Hyy' IH ]; auto.
  apply IH in Hyz.
  eapply rt1n_trans; eauto.
Qed.

Theorem steps_Lapp_l:
  forall e1 e1' e2,
    is_value e2 ->
    steps e1 e1' ->
    steps (Lappl e1 e2) (Lappl e1' e2).
Proof.
  induction 2.
  - reflexivity.
  - eapply rt1n_trans; eauto.
    apply step_Lappl_l; eauto.
Qed.

Theorem steps_Lapp_r:
  forall e1 e2 e2',
    steps e2 e2' ->
    steps (Lappl e1 e2) (Lappl e1 e2').
Proof.
  induction 1.
  - reflexivity.
  - eapply rt1n_trans; eauto.
    eapply step_Lappl_r; eauto.
Qed.

(** ** Correspondance betwen Big-step and Small-step *)
Theorem eval_implies_steps:
  forall e v, eval_cbv e v -> steps e v.
Proof.
  induction 1.
  - reflexivity.
  - assert (Hval : is_value e2') by (eapply eval_to_value; eauto).
    etransitivity.
    eapply steps_Lapp_r; eauto.
    etransitivity.
    eapply steps_Lapp_l; eauto.
    etransitivity; eauto.
    eapply rt1n_trans.
    apply step_beta; eauto.
    reflexivity.
Qed.

Theorem step_eval:
  forall e1 e2 v,
    step_cbv e1 e2 -> eval_cbv e2 v -> eval_cbv e1 v.
Proof.
  intros e1 e2 v Hstep. revert v.
  induction Hstep as [ e1 e2 e2' Hstep IH | | ]; intros v.
  - intros Heval. inversion Heval; subst; try easy.
    econstructor; eauto.
  - intros Heval. inversion Heval; subst; try easy.
    econstructor; eauto.
  - intros Heval. econstructor; eauto.
    apply eval_value. now constructor.
    now apply eval_value.
Qed.

Theorem steps_eval:
  forall e1 e2 v,
    steps e1 e2 -> eval_cbv e2 v -> eval_cbv e1 v.
Proof.
  intros e1 e2 v H Heval.
  induction H as [ | e1 e1' e2 H1 H2 IH ]; auto.
  specialize (IH Heval).
  eapply step_eval; eauto.
Qed.

Theorem steps_imlpies_eval:
  forall e v, steps e v -> is_value v -> eval_cbv e v.
Proof.
  induction 1; intros.
  - now apply eval_value.
  - specialize (IHclos_refl_trans_1n H1).
    eapply steps_eval; eauto.
    eapply rt1n_trans; eauto.
    reflexivity.
Qed.

Notation "M ->b N" := (step_cbv M N) (at level 50).
Notation "M ->b* N" := (steps M N) (at level 50).

(** ** fresh variables *)

Fixpoint is_free (M : term) (x : var) : Prop :=
  match M with
  | Lvar y => x = y
  | Labs y M => x <> y /\ is_free M x
  | Lappl M N => is_free M x \/ is_free N x
  end.

Fixpoint fresh (M : term) : var :=
  match M with
  | Lvar x => S x
  | Labs x M => fresh M
  | Lappl M N => max (fresh M) (fresh N)
  end.

Definition is_fresh (M : term) (x : var) : Prop :=
  ~is_free M x.

Theorem fresh_gt_free:
  forall M x, is_free M x -> fresh M > x.
Proof.
  induction M; intros y Hy; simpl in *.
  - lia.
  - destruct Hy as [Hy%IHM1 | Hy%IHM2]; lia.
  - now destruct Hy as [_ H2%IHM].
Qed.

Theorem fresh_is_fresh:
  forall M, is_fresh M (fresh M).
Proof.
  intros M Hx%fresh_gt_free. lia.
Qed.

(** ** Curch Encodings of Basic Datatypes *)

(** *** Booleans *)

Definition church_true := Labs 0 (Labs 1 (Lvar 0)).

Definition church_false := Labs 0 (Labs 1 (Lvar 1)).

Definition church_if (c t e : term) := Lappl (Lappl c t) e.

Definition church_and (b1 b2 : term) := church_if b1 b2 church_false.

Definition church_or (b1 b2 : term) := church_if b1 church_true b2.

(** *** Pairs *)

Definition church_pair (M : term) (N : term) : term :=
  let x := max (fresh M) (fresh N) in
  Labs x (Lappl (Lappl (Lvar x) M) N).

Definition church_fst (P : term) : term := Lappl P (Labs 0 (Labs 1 (Lvar 0))).

Definition church_snd (P : term) : term := Lappl P (Labs 0 (Labs 1 (Lvar 1))).

(** *** Integers *)

Definition church_zero : term :=
  Labs 1 (Labs 0 (Lvar 0)).

Definition church_succ (n : term) : term :=
  let x := fresh n in
  let f := S x in
  Labs f (Labs x (Lappl (Lvar f) (Lappl (Lappl n (Lvar f)) (Lvar x)))).

Fixpoint church_nat (n : nat) : term :=
  match n with
  | 0   => church_zero
  | S n => church_succ (church_nat n)
  end.

(* 

Fixpoint church_int_free (n : nat) : term :=
  match n with
  | 0 => Lvar 0
  | S n' => Lappl (Lvar 1) (church_int_free n')
end.

Definition church_int (n : nat) : term :=
  Labs 1 (Labs 0 (church_int_free n)).

Definition church_succ (N : term) : term :=
    Labs 2 (Labs 0 (Labs 1 ((Lappl (Lvar 2) (Lappl (Lappl (Lvar 2) (Lvar 0)) (Lvar 1)))))).

Definition church_succ2 (N : term) : term :=
  match N with
  | Lvar _ => N
  | Lappl _ _ => N
  | Labs f N' =>
    match N' with
    | Lvar _ => N
    | Lappl _ _ => N
    | Labs x N'' => Labs f (Labs x (Lappl (Lvar f) N''))
    end
end.

(* there is a problem with this... *)
Definition church_pred (N : term) : term :=
  church_snd
  (Lappl (Lappl N (Labs 2 (Lappl (Lvar 2) (Labs 0 (Labs 1 (Labs 3 (Lappl (Lappl (Lvar 3) (church_succ (Lvar 1))) (Lvar 1)))))))) (church_pair (church_int 0) (church_int 0))).

Definition church_plus (M N : term) (s z : var) : term :=
  Labs s (Labs z (Lappl (Lappl N (Lvar s)) (Lappl (Lappl M (Lvar s)) (Lvar z)))).

Definition church_minus (M N : term) : term :=
  Lappl (Lappl M (Labs 0 (church_pred (Lvar 0)))) N.

Definition church_times (M N : term) : term :=
  let x := max (fresh M) (fresh N) in
  let y := S x in
  Labs x (Labs y (Lappl (Lappl N (Lvar x)) (Lappl (Lappl M (Lvar x)) (Lvar y)))).

Definition church_gtz (M : term) : term :=
  Lappl (Lappl M (Labs 0 church_true)) church_false.

*)

(** *** Turing fixpoint *)

Definition turing_fixpoint_half : term := 
  Labs 1 (Labs 0 (Lappl (Lvar 0) (Lappl (Lappl (Lvar 1) (Lvar 1)) (Lvar 0)))).

Definition turing_fixpoint : term :=
  Lappl turing_fixpoint_half turing_fixpoint_half.

Definition turing_fixpoint_applied (M : term) : term :=
  Lappl M (Lappl (turing_fixpoint) M).

Lemma step_steps:
  forall e1 e2, step_cbv e1 e2 -> steps e1 e2.
Proof.
  intros e1 e2 H.
  eapply rt1n_trans; eauto.
  reflexivity.
Qed.

Notation "'λ' x ';' e" := (Labs x e) (at level 90).
Notation "'⟨' e1 e2 '⟩'" := (Lappl e1 e2) (at level 90).
Notation "'#' n" := (Lvar n) (at level 90).

Lemma turing_fixpoint_is_fp:
  forall f y,
    is_value f ->
    is_value y ->
    Lappl (Lappl turing_fixpoint f) y ->b*
    Lappl (Lappl f (Lappl turing_fixpoint f)) y.
Proof.
  intros f x Hf Hx.
  etransitivity.
  eapply steps_Lapp_l; auto.
  eapply steps_Lapp_l; auto.
  unfold turing_fixpoint.
  eapply rt1n_trans.
  eapply step_beta. constructor.
  reflexivity. simpl.
  etransitivity.
  eapply steps_Lapp_l; auto.
  eapply step_steps.
  apply step_beta; auto.
  simpl. reflexivity.
Qed.


(** beta-reduction properties *)

(* Lemma beta_red_is_transitive : transitive term (beta_star).
Proof. unfold transitive. intros *. unfold beta_star. apply trans. Qed.

Lemma bredstar_contextual_abs :
  forall (x : var) (M M': term), M ->b* M' -> Labs x M ->b* Labs x M'.
Proof. intros. induction H as [M'|M1 M2 M3 Red1 IHred1 Red2 IHred2|M N Honestep].
  - apply refl.
  - apply trans with (y := Labs x M2).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_lambda with (x := x) in Honestep. apply Honestep.
Qed.

Lemma bredstar_contextual_appl_function :
  forall (M M' N : term), M ->b* M' -> Lappl M N ->b* Lappl M' N.
Proof. intros *. intros red. induction red as [M'|M1 M2 M3 Red1 IHred1 Red2 IHred2|M M' Honestep].
  - apply refl.
  - apply trans with (y := Lappl M2 N).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_function. apply Honestep.
Qed.

Lemma bredstar_contextual_appl_argument :
  forall (M N N': term), N ->b* N' -> Lappl M N ->b* Lappl M N'.
Proof. intros *. intros red.  induction red as [N'|N1 N2 N3 Red1 IHred1 Red2 IHred2|N N' Honestep].
  - apply refl.
  - apply trans with (y := Lappl M N2).
    + apply IHred1.
    + apply IHred2.
  - apply onestep. apply contextual_argument. apply Honestep.
Qed.

Lemma bredstar_contextual_appl :
  forall (M M' N N': term), M ->b* M' -> N ->b* N' -> Lappl M N ->b* Lappl M' N'.
Proof. intros *. intros redlhs redrhs. apply trans with (y := Lappl M' N).
  - apply bredstar_contextual_appl_function. apply redlhs.
  - apply bredstar_contextual_appl_argument. apply redrhs.
Qed.


Lemma substitution_fresh_l : forall (M N : term) (x : var), in_list (fvL M) x = false -> substitution M N x = M.
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


Lemma substitution_comm : forall (x y : var) (M N N' : term),
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


(** evaluator *)
Fixpoint leftmost_outermost_beta_aux (M : term) : term * bool := match M with
  | Lvar x => (Lvar x, false)
  | Lappl (Labs x M') N' => (substitution M' N' x, true)
  | Lappl M' N' => let res := (leftmost_outermost_beta_aux M') in
    if snd res then
      (Lappl (fst res) N', true)
    else
      let res' := leftmost_outermost_beta_aux N' in (Lappl M' (fst res'), snd res')
  | Labs x M' => let res := leftmost_outermost_beta_aux M' in (Labs x (fst res), snd res)
end.

Definition leftmost_outermost_beta (M : term) : term :=
      fst (leftmost_outermost_beta_aux M).

Lemma modification_lmom_aux : forall (M : term), snd (leftmost_outermost_beta_aux M) = false ->
                                                        M = leftmost_outermost_beta M.
Proof. intros. induction M.
  - unfold leftmost_outermost_beta. reflexivity.
  - unfold leftmost_outermost_beta. simpl. destruct M1.
    + simpl. simpl in H. apply IHM2 in H. unfold leftmost_outermost_beta in H.
      rewrite <- H. reflexivity.
    + destruct (snd (leftmost_outermost_beta_aux (Lappl M1_1 M1_2))) eqn:eq.
      * simpl in H. simpl in eq. rewrite eq in H. inversion H.
      * simpl. simpl in H. simpl in eq. rewrite eq in H. simpl in H. apply IHM2 in H.
        unfold leftmost_outermost_beta in H. rewrite <- H. reflexivity.
    + simpl in H. discriminate H.
  - unfold leftmost_outermost_beta. simpl. apply IHM in H. unfold leftmost_outermost_beta in H. rewrite <- H.
    reflexivity.
Qed.

Lemma first_let : forall {X Y} (p : X*Y), (let (x,_) := p in x) = fst p.
Proof. intros; destruct p.
       reflexivity. Qed.

Lemma leftmost_subset_beta : forall (M : term), M ->b* (leftmost_outermost_beta M).
Proof. induction M.
  - unfold leftmost_outermost_beta. simpl. apply refl.
  - unfold leftmost_outermost_beta. simpl. destruct M1.
    + simpl. apply bredstar_contextual_appl_argument. apply IHM2.
    + destruct (snd (leftmost_outermost_beta_aux (Lappl M1_1 M1_2))).
      * unfold fst. apply bredstar_contextual_appl_function. rewrite first_let.
        unfold leftmost_outermost_beta in IHM1. apply IHM1.
      * simpl. apply bredstar_contextual_appl_argument. unfold leftmost_outermost_beta in IHM2.
        apply IHM2.
   + simpl. apply onestep. apply redex_contraction.
  - unfold leftmost_outermost_beta. simpl. apply bredstar_contextual_abs. unfold leftmost_outermost_beta in IHM.
    apply IHM.
Qed.

Lemma leftmost_step : forall (M N : term), leftmost_outermost_beta M ->b* N -> M ->b* N.
Proof. intros. apply trans with (y := leftmost_outermost_beta M).
  + apply leftmost_subset_beta.
  + apply H.
Qed.

Lemma eql_eq : forall (M N : term), M = N <-> M =?l N = true.
Proof. intros. split.
  - generalize dependent M. induction N.
    + intros M H; rewrite H. simpl. rewrite Nat.eqb_refl. reflexivity.
    + intros M H; rewrite H. simpl. rewrite IHN1. rewrite IHN2. reflexivity.
      reflexivity. reflexivity.
    + intros M H. rewrite H. simpl. rewrite Nat.eqb_refl. simpl. rewrite IHN. reflexivity. reflexivity.
  - Admitted.

Inductive lambda_address : Type :=
  | here
  | function : lambda_address -> lambda_address
  | argument : lambda_address -> lambda_address
  | through_abs : lambda_address -> lambda_address.

Fixpoint beta_red_address (M : term) (a : lambda_address) : term := match a, M with
  | here, Lappl (Labs x M') N' => substitution M' N' x
  | function a', Lappl M' N' => Lappl (beta_red_address M' a') N'
  | argument a', Lappl M' N' => Lappl M' (beta_red_address N' a')
  | through_abs a', Labs x M' => Labs x (beta_red_address M' a')
  | _, _ => M
end.

Lemma beta_red_address_subset_beta : forall (M : term) (a : lambda_address),
        M ->b* (beta_red_address M a).
Proof. intros. generalize dependent M. induction a.
  - destruct M.
    + simpl. apply refl.
    + simpl. destruct M1.
      * apply refl.
      * apply refl.
      * apply onestep. apply redex_contraction.
    + simpl. apply refl.
  - destruct M.
    + simpl. apply refl.
    + simpl. apply bredstar_contextual_appl_function. apply IHa.
    + simpl. apply refl.
  - destruct M.
    + apply refl.
    + simpl. apply bredstar_contextual_appl_argument. apply IHa.
    + apply refl.
  - destruct M.
    + apply refl.
    + apply refl.
    + simpl. apply bredstar_contextual_abs. apply IHa.
Qed.

Lemma adress_step : forall (M N : term) (a : lambda_address), (beta_red_address M a) ->b* N ->
                                                                              M ->b* N.
Proof. intros. apply trans with (y := beta_red_address M a).
  + apply beta_red_address_subset_beta.
  + apply H.
Qed.

(** lemmas about constuctors *)

Lemma succ2_spec : forall (n : nat), church_succ2 (church_int n) = church_int (S n).
Proof. intros. unfold church_succ2. unfold church_int. simpl. reflexivity. Qed.

(** substitution lemmas *)
Lemma subst_lambda_cont : forall (M N : term) (x y : var), x <> y ->
                                    substitution (Labs x M) N y = Labs x (substitution M N y).
Proof. intros. simpl. apply Nat.eqb_neq in H. rewrite Nat.eqb_sym. rewrite H. reflexivity. Qed.

Lemma subst_appl_cont : forall (M N P : term) (x : var),
                                    substitution (Lappl M N) P x = Lappl (substitution M P x) (substitution N P x).
Proof. reflexivity. Qed.

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

Lemma church_pred_free : forall (n : nat), (Lappl
     (Lappl (church_int n)
        (Labs 2
           (Lappl (Lvar 2)
              (Labs 0 (Labs 1 (Labs 3 (Lappl (Lappl (Lvar 3) (church_succ (Lvar 1))) (Lvar 1))))))))
     (church_pair (church_int 0) (church_int 0))) ->b* church_pair (church_int n) (church_int (Nat.pred n)).
Proof. induction n as [|n' IHn'].
  - simpl. unfold church_int. unfold church_pred. unfold church_int_free.
    apply leftmost_step. apply leftmost_step. apply leftmost_step. apply leftmost_step.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl. apply refl.
  - simpl. unfold church_int. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.


Lemma church_pred_is_pred : forall (n : nat), church_pred (church_int n) ->b* church_int (Nat.pred n).
Proof. intros. destruct n as [|n'].
  - simpl. unfold church_int. unfold church_pred. unfold church_int_free.
    apply leftmost_step. apply leftmost_step. apply leftmost_step. apply leftmost_step.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl. apply refl.
  - simpl. unfold church_pred. unfold church_int. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.
    apply leftmost_step. unfold leftmost_outermost_beta. simpl.


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
Qed. *)