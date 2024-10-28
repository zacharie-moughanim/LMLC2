Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Definitions.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import PeanoNat.

From LMLCProof Require Import Utils Source Object Transpiler.

(** Beta-Reduction properties *)

Lemma beta_red_is_reflexive : reflexive lambda_term (beta_star).
Proof. unfold reflexive. intro x. unfold beta_star. apply refl.
Qed.

Lemma S_predn : forall (n : nat), n = 0 \/ S (pred n) = n.
Proof. 
  intros [|n].
  - simpl. left. reflexivity.
  - simpl. right. reflexivity.
Qed.

Lemma S_predn' : forall (n : nat), 0 < n -> S (pred n) = n.
Proof. 
  intros *. intro H.  Abort.


Lemma pred_minus : forall (n : nat), pred n = n - 1.
Proof.
  destruct n.
  - reflexivity.
  - simpl. rewrite minus_n_0. reflexivity.
Qed.

Lemma le_n_plus_n_m : forall (n m : nat), 1 <= m -> n <= n + m - 1.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m H. simpl. apply all_positive_more_than_zero.
  - simpl. intros m H. apply IHn' in H as H'. rewrite minus_n_0. apply le_n_S in H'.
Admitted.

Lemma succ_church : forall n : nat,
  church_succ2 (church_int n) = church_int (S n).
Proof.
  intros n. unfold church_int. unfold church_int_free. unfold church_succ2.
  destruct n as [|n'].
  - reflexivity.
  - reflexivity.
Qed.

Example test1 : forall (n m : nat), Nat.pred (S n - m) = n - m.
Proof. Admitted.

Example H3Modif : forall (n0 : nat) (h0 : lambda_term) (ht0 : lambda_term) (tlt0 : list lambda_term),
     (forall n : nat,
     match find_opt (h0 :: ht0 :: tlt0) n with
     | Some a =>
         match find_opt (h0 :: ht0 :: tlt0) (S n) with
         | Some b => a ->b b
         | None => True
         end
     | None => True
     end) -> match find_opt (h0 :: ht0 :: tlt0) (S n0) with
     | Some a =>
         match find_opt (h0 :: ht0 :: tlt0) (S (S n0)) with
         | Some b => a ->b b
         | None => True
         end
     | None => True
     end.
Proof. intros *. intro H3. apply H3. Qed.

Lemma beta_red_is_transitive : transitive lambda_term (beta_star).
Proof. unfold transitive. intros *. unfold beta_star. apply trans. Qed.

Lemma beta_subset_beta_star : forall (M N : lambda_term), M ->b N -> M ->b* N.
Proof. intros M N H. apply onestep. apply H. Qed.

Lemma beta_star_contextual_abs :
  forall (x : var) (M M': lambda_term), M ->b* M' -> Labs x M ->b* Labs x M'.
Admitted.

Lemma beta_star_contextual_appl :
  forall (M M' N N': lambda_term), M ->b* M' /\ N ->b* N' -> Lappl M N ->b* Lappl M' N'.
Admitted.

Lemma beta_star_contextual_appl'l :
  forall (M M' N: lambda_term), M ->b* M' -> Lappl M N ->b* Lappl M' N.
Admitted.

Lemma beta_star_contextual_appl'r :
  forall (M N N': lambda_term), N ->b* N' -> Lappl M N ->b* Lappl M N'.
Admitted.

Lemma substitution_fresh_l : forall (M N : lambda_term) (x : var), in_list (fvL M) x = false -> substitution M N x = M.
Proof. intros * H. Admitted.

(* MAIN PROOF *)
(* WE NEED ALPHA-EQUIVALENCE... *)
Lemma lmlc_substitution : forall (M N : ml_term) (x : var),
                          lmlc (ml_substitution M N x) = substitution (lmlc M) (lmlc N) x.
Proof. induction M as [ x | M1 IHappl1 M2 IHappl2 | x M' IHfunbody| f x M' IHfixfunbody
                      | M1 IHplus1 M2 IHplus2 | M1 IHminus1 M2 IHminus2 | M1 IHtimes1 M2 IHtimes2 | n
                      | M' IHgtz
                      | | C IHifc T IHift E IHife
                      | HD IHconshd TL IHconsnil| |LST IHfoldlst OP IHfoldop INIT IHfoldinit
                      | P1 IHpair1 P2 IHpair2 | P IHfst | P IHsnd ].
(* M = x *)
  - intros *. simpl. destruct (x0 =? x).
    + reflexivity.
    + reflexivity.
(* M = (M1)M2 *)
  - intros *. simpl. rewrite IHappl1. rewrite IHappl2. reflexivity.
(* M = fun x -> M' *)
  - intros *. simpl. destruct (x0 =? x).
    + reflexivity.
    + simpl. rewrite IHfunbody. reflexivity.
(* M = fixfun f x -> M' *)
  - admit.
(* M = M1 + M2 *)
  - intros N y. destruct (in_list ((fvL (lmlc M1)) ++ (fvL (lmlc M2))) y) eqn:eq.
    + simpl. assert (eq' : in_list (fvL (lmlc M1) ++ fvL (lmlc M2)) y = true). { apply eq. } apply fresh_spec in eq. rewrite Nat.eqb_sym. rewrite eq.
      assert (H: y =? fresh (fresh (fvL (lmlc M1) ++ fvL (lmlc M2)) :: fvL (lmlc M1) ++ fvL (lmlc M2)) = false).
      {
        assert (H' : in_list ((fresh (fvL (lmlc M1) ++ fvL (lmlc M2))) :: fvL (lmlc M1) ++ fvL (lmlc M2)) y = true).
        {
          simpl. rewrite Nat.eqb_sym. rewrite eq. apply eq'.
        }
        apply fresh_spec in H'. rewrite Nat.eqb_sym. apply H'.
      }
      rewrite H. unfold church_plus. admit.
    + admit.
(* M = M1 - M2 *)
  - admit.
(* M = M1 * M2 *)
  - admit.
(* M = n [in NN] *)
  - intros. simpl. destruct (x =? 1) eqn:eqx1.
    + reflexivity.
    + destruct (x =? 0) eqn:eqx0.
      * reflexivity.
      * { induction n as [|n' IHn'].
          - simpl. rewrite eqx0. reflexivity.
          - admit.
        }
(* M = 0 < M *)
  - simpl. symmetry. rewrite <- IHgtz. symmetry. unfold church_gtz. unfold church_true. unfold church_false. admit.
(* M = true *)
  - intros. simpl. destruct b.
    + unfold church_true. destruct (x =? 0) eqn:eqx0.
      * simpl. rewrite eqx0. reflexivity.
      * destruct (x =? 1) eqn:eqx1.
        -- simpl. rewrite eqx0. rewrite eqx1. reflexivity.
        -- simpl. rewrite eqx0. rewrite eqx1. reflexivity.
    + unfold church_false. destruct (x =? 0) eqn:eqx0.
      * simpl. rewrite eqx0. reflexivity.
      * destruct (x =? 1) eqn:eqx1.
        -- simpl. rewrite eqx0. rewrite eqx1. reflexivity.
        -- simpl. rewrite eqx0. rewrite eqx1. reflexivity.
(* M = If C then T else E *)
  - admit.
(* M = HD::TL *)
  - admit.
(* M = [] *)
  - intros. simpl. destruct (x =? 0) eqn:eqx0.
      * simpl. reflexivity.
      * destruct (x =? 1) eqn:eqx1.
        -- reflexivity.
        -- reflexivity.
(* M = Fold_right LST OP INIT *)
  - admit.
(* M = <P1,P2> *)
  - admit.
(* M = fst P *)
  - intros. simpl. rewrite IHfst. destruct (x =? 1) eqn:eqx1.
    + admit.
    + destruct (x =? 2) eqn:eqx2.
      * admit.
      * admit.
(* M = snd P *)
  - intros. simpl. rewrite IHsnd. destruct (x =? 1) eqn:eqx1.
    + reflexivity.
    + destruct (x =? 2) eqn:eqx2.
      * reflexivity.
      * reflexivity.
Admitted.
(* still a lot of prb with free variables when constructing terms *)


(**
If you want to induct :
[ y | L1 IHappl1' L2 IHappl2' | y L IHfunbody'| g y L IHfixfunbody'
| L1 IHplus1' L2 IHplus2' | L1 IHminus1' L2 IHminus2' | L1 IHtimes1' L2 IHtimes2' | m
| L IHgtz'
| | | C' IHifc' T' IHift' E' IHife'
| HD' IHconshd' TL' IHconsnil' | | LST' IHfoldlst' OP' IHfoldop' INIT' IHfoldinit'
| P1' IHpair1' P2' IHpair2' | P' IHfst' | P' IHsnd' ]


If you want to destruct :
[ y | L1 L2 | y L | g y L
| L1 L2 | L1 L2 | L1 L2 | m
| L
| | | C' T' E'
| HD' TL' | | LST' OP' INIT'
| P1' P2' | P' | P' ]

*)

Theorem lmlc_is_correct : forall (M N : ml_term), M ->ml N -> (lmlc M) ->b* (lmlc N).
Proof. intros. Print ml_reduction.
induction H as
[
    x M M' HM IHfun_contextual
  | f x M M' HM IHfixfun_contextual
  | M M' N HM IHappl_contextual
  | M N N' HN IHappl_contextual
  | M M' N HM IHplus_contextual
  | M N N' HN IHplus_contextual
  | M M' N HM IHminus_contextual
  | M N N' HN IHminus_contextual
  | M M' N HM IHtimes_contextual
  | M N N' HN IHtimes_contextual
  | M M' N IHgtz_contextual
  | C C' T E HC IHif_contextual
  | C T T' E HT IHif_contextual
  | C T E E' HE IHif_contextual
  | HD HD' TL HHD IHcons_contextual
  | HD TL TL' HTL IHcons_contextual
  | LST LST' FOO INIT HLST IHfold_contextual
  | LST FOO FOO' INIT HFOO IHfold_contextual
  | LST FOO INIT INIT' HINIT IHfold_contextual
  | P1 P1' P2 HP1 IHpair
  | P1 P2 P2' HP2 IHpair
  | P P' HP IHfst
  | P P' HP IHsnd
  | x M N
  | f x M IHfixfun
  | n m
  | n m
  | n m
  | n
  | FOO INIT
  | HD TL FOO INIT
  | P1 P2
  | P1 P2
].
(* contextual cases *)
  - simpl. apply bredstar_cont_lambda. apply IHfun_contextual.
  - simpl. unfold turing_fixpoint_applied. apply bredstar_cont_appl.
    + apply bredstar_cont_lambda. apply bredstar_cont_lambda. apply IHfixfun_contextual.
    + apply bredstar_cont_appl.
      * apply refl.
      * apply bredstar_cont_lambda. apply bredstar_cont_lambda. apply IHfixfun_contextual.
  - simpl. apply bredstar_cont_appl.
    + apply IHappl_contextual.
    + apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply refl.
    + apply IHappl_contextual.
  - admit. (* we ought to prove some more contextuality lemmas about church_plus, church_minus, etc. *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - simpl. unfold church_gtz. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply IHgtz_contextual.
      * apply refl.
    + apply refl.
  - simpl. unfold church_if. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply IHif_contextual.
      * apply refl.
    + apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply refl.
      * apply IHif_contextual.
    + apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply refl.
    + apply IHif_contextual.
  - simpl. apply bredstar_cont_lambda. apply bredstar_cont_lambda. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply refl.
      * apply IHcons_contextual.
    + apply refl.
  - simpl. apply bredstar_cont_lambda. apply bredstar_cont_lambda. apply bredstar_cont_appl.
    + apply refl.
    + apply bredstar_cont_appl.
      * apply bredstar_cont_appl.
        -- apply IHcons_contextual.
        -- apply refl.
      * apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply IHfold_contextual.
      * apply refl.
    + apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply refl.
      * apply IHfold_contextual.
    + apply refl.
  - simpl. apply bredstar_cont_appl.
    + apply refl.
    + apply IHfold_contextual.
  - simpl. assert (alpharename1 : Labs (fresh (fvML P1 ++ fvML P2))
  (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2))) (lmlc P1)) (lmlc P2)) =
Labs (fresh (fvML P1 ++ fvML P1' ++ fvML P2))
  (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P1' ++ fvML P2))) (lmlc P1)) (lmlc P2))).
  { admit. } rewrite alpharename1. clear alpharename1.
  assert
  ( alpharename2 :
  Labs (fresh (fvML P1' ++ fvML P2))
    (Lappl (Lappl (Lvar (fresh (fvML P1' ++ fvML P2))) (lmlc P1')) (lmlc P2)) =
  Labs (fresh (fvML P1 ++ fvML P1' ++ fvML P2))
    (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P1' ++ fvML P2))) (lmlc P1')) (lmlc P2))
  ). { admit. }
  rewrite alpharename2. clear alpharename2. apply bredstar_cont_lambda. apply bredstar_cont_appl.
    + apply bredstar_cont_appl.
      * apply refl.
      * apply IHpair.
    + apply refl.
  - simpl. assert (alpharename1 : Labs (fresh (fvML P1 ++ fvML P2))
  (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2))) (lmlc P1)) (lmlc P2)) =
  Labs (fresh (fvML P1 ++ fvML P2' ++ fvML P2))
    (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2' ++ fvML P2))) (lmlc P1)) (lmlc P2))).
  {
    admit.
  }
  rewrite alpharename1. clear alpharename1.
  assert (alpharename2 : Labs (fresh (fvML P1 ++ fvML P2'))
  (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2'))) (lmlc P1)) (lmlc P2')) =
  Labs (fresh (fvML P1 ++ fvML P2' ++ fvML P2))
  (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2' ++ fvML P2))) (lmlc P1)) (lmlc P2'))).
  {
    admit.
  }
  rewrite alpharename2. clear alpharename2. apply bredstar_cont_lambda. apply bredstar_cont_appl.
    + apply refl.
    + apply IHpair.
  - simpl. apply bredstar_cont_appl.
    + apply IHfst.
    + admit.
  - simpl. apply bredstar_cont_appl.
    + apply IHsnd.
    + apply refl.
(* redex case *)
  - simpl. rewrite lmlc_substitution. apply onestep. apply redex_contraction.
(* fixfun case *)
  - simpl. unfold turing_fixpoint_applied. apply bredstar_cont_appl.
    + apply refl.
    + apply trans with (y := Lappl (Labs 0 (Lappl (Lvar 0) (Lappl turing_fixpoint (Lvar 0)))) (Labs f (Labs x (lmlc M)))).
      * unfold turing_fixpoint. apply bredstar_cont_appl.
        -- apply onestep. apply redex_contraction.
        -- apply refl.
      * apply onestep. apply redex_contraction.
(* plus case *)
  - admit.
(* minus case *)
  - admit.
(* times case *)
  - admit.
(* greather than zero case *)
  - destruct (0 <? n) eqn:ineqn.
    + simpl. apply Nat.ltb_lt in ineqn. admit.
    + apply Nat.ltb_nlt in ineqn. apply Nat.nlt_ge in ineqn. inversion ineqn. simpl. unfold church_gtz.
      unfold church_int. unfold church_int_free. apply trans with (y := Lappl (Labs 0 (Lvar 0)) (church_false)).
      * assert ((Labs 0 (Lvar 0)) = substitution (Labs 0 (Lvar 0)) (Labs 0 church_true) 1). { reflexivity. }
        rewrite H0. assert (Lappl (Lappl (Labs 1 (substitution (Labs 0 (Lvar 0)) (Labs 0 church_true) 1)) (Labs 0 church_true)) = Lappl (Lappl (Labs 1 (Labs 0 (Lvar 0))) (Labs 0 church_true))).
        { reflexivity. } rewrite H1. apply bredstar_cont_appl.
        -- apply onestep. apply redex_contraction.
        -- apply refl.
      * apply onestep. assert (church_false = substitution (Lvar 0) church_false 0). { reflexivity. }
        rewrite H0. assert (Lappl (Labs 0 (Lvar 0)) (substitution (Lvar 0) church_false 0) = Lappl (Labs 0 (Lvar 0)) (church_false)).
        { rewrite <- H0. reflexivity. } rewrite H1. apply redex_contraction.
(* fold base case *)
  - simpl. apply trans with (y := (Lappl (Labs 1 (Lvar 1)) (lmlc INIT))).
    + apply bredstar_cont_appl.
      * assert (Labs 1 (Lvar 1) = substitution (Labs 1 (Lvar 1)) (lmlc FOO) 0). { reflexivity. } rewrite H.
        assert (Lappl (Labs 0 (substitution (Labs 1 (Lvar 1)) (lmlc FOO) 0)) (lmlc FOO) = Lappl (Labs 0 (Labs 1 (Lvar 1))) (lmlc FOO) ).
        { reflexivity. } rewrite H0. apply onestep. apply redex_contraction.
      * apply refl.
    + apply onestep. apply redex_contraction.
(* fold induction step case *)
  - admit.
(* fst case *)
  - simpl. apply trans with (y := Lappl (Lappl (Labs 1 (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1))) (lmlc P1)) (lmlc P2)).
    + apply onestep. assert (Lappl (Lappl (Labs 1 (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1))) (lmlc P1)) (lmlc P2) =
                             substitution (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2))) (lmlc P1)) (lmlc P2))
                             (Labs 1 (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1))) (fresh (fvML P1 ++ fvML P2))).
      * simpl. rewrite Nat.eqb_refl. assert (substitution (lmlc P1) (Labs 1 (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1))) (fresh (fvML P1 ++ fvML P2)) = lmlc P1).
        { apply substitution_fresh_l. apply Bool.not_true_iff_false. intro H. apply in_list_app3 with (l2 := fvL (lmlc P2)) in H.
          rewrite fvML_L in H. rewrite fvML_L in H. apply fresh_spec in H. rewrite Nat.eqb_refl in H. discriminate H.
        } assert (substitution (lmlc P2) (Labs 1 (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1))) (fresh (fvML P1 ++ fvML P2)) = lmlc P2).
        { apply substitution_fresh_l. apply Bool.not_true_iff_false. intro G. apply in_list_app3 with (l2 := fvL (lmlc P1)) in G.
          rewrite fvML_L in G. rewrite fvML_L in G. rewrite in_list_app_comm in G. apply fresh_spec in G. rewrite Nat.eqb_refl in G. discriminate G.
        } rewrite H. rewrite H0. reflexivity.
      * rewrite H. apply redex_contraction.
    + apply trans with (y := Lappl (Labs (fresh (fvML P1 ++ fvML P2)) (lmlc P1)) (lmlc P2)).
      * apply bredstar_cont_appl.
        -- apply onestep. assert (Labs (fresh (fvML P1 ++ fvML P2)) (lmlc P1) = substitution (Labs (fresh (fvML P1 ++ fvML P2)) (Lvar 1)) (lmlc P1) 1).
            { simpl.  } rewrite H. apply redex_contraction.
        -- apply refl.
      * apply onestep. assert (lmlc P1 = substitution (lmlc P1) (lmlc P2) (fresh (fvML P1 ++ fvML P2))). {
          admit.
        } rewrite H.
        assert (Lappl (Labs (fresh (fvML P1 ++ fvML P2)) (substitution (lmlc P1) (lmlc P2) (fresh (fvML P1 ++ fvML P2)))) = Lappl (Labs (fresh (fvML P1 ++ fvML P2)) (lmlc P1))). { rewrite <- H. reflexivity. }
        rewrite H0. apply redex_contraction.
(* snd case *)
  - simpl. apply trans with (y := Lappl (Lappl (Labs 1 (Labs 2 (Lvar 2))) (lmlc P1)) (lmlc P2)).
    + apply onestep. assert (Lappl (Lappl (Labs 1 (Labs 2 (Lvar 2))) (lmlc P1)) (lmlc P2) =
                             substitution (Lappl (Lappl (Lvar (fresh (fvML P1 ++ fvML P2))) (lmlc P1)) (lmlc P2))
                             (Labs 1 (Labs 2 (Lvar 2))) (fresh (fvML P1 ++ fvML P2))).
      * simpl. rewrite Nat.eqb_refl. assert (substitution (lmlc P1) (Labs 1 (Labs 2 (Lvar 2))) (fresh (fvML P1 ++ fvML P2)) = lmlc P1).
        { admit. } assert (substitution (lmlc P2) (Labs 1 (Labs 2 (Lvar 2))) (fresh (fvML P1 ++ fvML P2)) = lmlc P2).
        { admit. } rewrite H. rewrite H0. reflexivity.
      * rewrite H. apply redex_contraction.
    + apply trans with (y := Lappl (Labs 2 (Lvar 2)) (lmlc P2)).
      * apply bredstar_cont_appl.
        -- apply onestep. assert (Labs 2 (Lvar 2) = substitution (Labs 2 (Lvar 2)) (lmlc P1) 1).
            { reflexivity. } rewrite H. apply redex_contraction.
        -- apply refl.
      * apply onestep. assert (lmlc P2 = substitution (Lvar 2) (lmlc P2) 2). { reflexivity. } rewrite H.
        assert (Lappl (Labs 2 (Lvar 2)) (substitution (Lvar 2) (lmlc P2) 2) = Lappl (Labs 2 (Lvar 2)) (lmlc P2) ). { rewrite <- H. reflexivity. }
        rewrite H0. apply redex_contraction.












