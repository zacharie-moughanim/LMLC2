Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Definitions.
From Coq Require Import Lists.List.
Import ListNotations.
Require Import PeanoNat.
(* We require this : *)
From LMLCProof Require Import Utils Source Object Transpiler.

(** Beta-Reduction properties *)

Lemma beta_red_is_reflexive : reflexive lambda_term (beta_star).
Proof. unfold reflexive. intro x. unfold beta_star.
       unfold refl_trans_closure. exists [x]. split.
  - simpl. reflexivity.
  - simpl. split.
    + reflexivity.
    + intro n. destruct n as [|n'].
      * reflexivity.
      * destruct (match n' with | 0 | _ => None end).
        ++ reflexivity.
        ++ reflexivity.
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
Proof. unfold transitive. intros *. unfold beta_star. unfold refl_trans_closure.
       intros H G. destruct H as [l0 H]. destruct H as [H1 H2]. destruct H2 as [H2 H3].
                   destruct G as [l1 G]. destruct G as [G1 G2]. destruct G2 as [G2 G3].
       exists (l0 ++ (tail l1)). split.
  - assert (K : find_opt l0 0 <> None).
  { rewrite H1. intro K'. discriminate K'. }
  apply find_opt_app1 with (l2 := l0)(l3 := (tail l1)) in K. rewrite K. rewrite H1. reflexivity.
  - split.
    + destruct (tail l1) as [|htl1 ttl1] eqn:eq.
      * rewrite <- app_nil_end. rewrite H2. rewrite <- G1. assert (L1Form : l1 = y :: (tail l1)).
        { destruct l1.
          - simpl. simpl in G1. discriminate G1.
          - simpl. simpl in G1. injection G1. intro G1'. rewrite G1'. reflexivity. }
        rewrite L1Form. simpl. rewrite <- G2. symmetry. rewrite L1Form. simpl.
        rewrite minus_n_0. rewrite eq. simpl. reflexivity.
      * assert (K : find_opt l0 (length (l0 ++ (tail l1)) - 1) = None).
        { rewrite length_app. apply find_opt_length.
          assert (ineq : length l0 + length (tail l1) - 1 = length l0 + (length (tail l1) - 1)).
          {
            assert (L1Form : l1 = y :: (tail l1)).
            { destruct l1.
              - simpl. simpl in G1. discriminate G1.
              - simpl. simpl in G1. injection G1. intro G1'. rewrite G1'. reflexivity. }
            rewrite L1Form. simpl. destruct (length l0).
              - simpl. reflexivity.
              - simpl. rewrite minus_n_0. rewrite plus_n_Sm. rewrite PeanoNat.Nat.sub_1_r.
                assert (S_predlengthl1 : length (tail l1) = 0 \/ S (pred (length (tail l1))) = length (tail l1)).
                { apply S_predn. } destruct S_predlengthl1.
                + rewrite eq in H. simpl in H. discriminate H.
                + rewrite H. reflexivity.
          }
          rewrite ineq. apply Plus.le_plus_l.
        }
        apply find_opt_app2 with (l2 := l0)(l3 := tail l1) in K. rewrite <- eq. rewrite K.
        assert (Num_is_lengthl1 : length (l0 ++ tail l1) - 1 - length l0 = length (tail l1) - 1).
        {
          rewrite length_app. rewrite test_plus_minus. reflexivity.
        }
        rewrite Num_is_lengthl1. assert (L1Form : l1 = y :: (tail l1)).
        { destruct l1.
          - simpl. simpl in G1. discriminate G1.
          - simpl. simpl in G1. injection G1. intro G1'. rewrite G1'. reflexivity. }
        rewrite L1Form in G2. assert (G2usable : find_opt (y :: tail l1) (length (y :: tail l1) - 1) =
                                                 find_opt (tail l1) (length (tail l1) - 1)).
        {
          simpl. rewrite minus_n_0. rewrite eq. simpl. rewrite minus_n_0. reflexivity.
        }
        rewrite G2usable in G2. apply G2.
    + intro n. destruct (find_opt l0 (S n)) eqn:eq.
      * assert (eq' : find_opt l0 (S n) <> None).
      { rewrite eq. unfold not. intro H. discriminate H. }
        apply find_opt_app1 with (l2 := l0)(l3 := tail l1) in eq'. rewrite eq'.
        assert (eq'' : find_opt l0 (S n) <> None).
      { rewrite eq. unfold not. intro H. discriminate H. }
        apply find_opt_S in eq''. apply find_opt_app1 with (l2 := l0)(l3 := tail l1) in eq''. rewrite eq''.
        apply H3.
      * destruct (find_opt l0 n) eqn:eq2.
        ++ assert (eq2' : find_opt l0 n <> None).
        { rewrite eq2. intro Tmp. discriminate Tmp. }
          apply find_opt_length_bound in eq2'.
          ** assert (eq2'' : find_opt l0 n <> None).
          { rewrite eq2. intro Tmp. discriminate Tmp. }
            apply find_opt_app1 with (l2 := l0)(l3 := tail l1) in eq2''. rewrite eq2''.
            apply find_opt_app2 with (l2 := l0)(l3 := tail l1) in eq. rewrite eq. rewrite eq2.
            rewrite eq2'. simpl. rewrite minus_n_n. destruct (tail l1) as [|htl1 ttl1] eqn:eqtl1.
            *** reflexivity.
            *** simpl. assert (l_is_y : Some l = Some y).
                {
                  rewrite <- eq2. apply f_equal_pred in eq2'. simpl in eq2'. rewrite pred_minus in eq2'.
                  rewrite <- H2. rewrite eq2'. reflexivity.
                }
                injection l_is_y. intro l_is_y'. rewrite l_is_y'. assert (G3' : match find_opt l1 0 with
                                                                               | Some a => match find_opt l1 1 with
                                                                                           | Some b => a ->b b
                                                                                           | None => True
                                                                                           end
                                                                               | None => True
                                                                               end).
              { apply G3. }
                rewrite G1 in G3'. assert (L1Form : l1 = y :: (tail l1)).
        { destruct l1.
          - simpl. simpl in G1. discriminate G1.
          - simpl. simpl in G1. injection G1. intro G1'. rewrite G1'. reflexivity. }
                rewrite L1Form in G3'. rewrite eqtl1 in G3'. simpl in G3'. apply G3'.
          ** apply eq.
        ++ assert (eq2' : find_opt l0 n = None). { apply eq2. }
            apply find_opt_app2 with (l2:=l0)(l3:=tail l1) in eq2. rewrite eq2.
            apply find_opt_app2 with (l2:=l0)(l3:=tail l1) in eq. rewrite eq.
            apply find_opt_length_2' in eq2'. apply PeanoNat.Nat.sub_succ_l in eq2'.
            rewrite eq2'. assert (L1Form : l1 = y :: (tail l1)).
            { destruct l1.
              - simpl. simpl in G1. discriminate G1.
              - simpl. simpl in G1. injection G1. intro G1'. rewrite G1'. reflexivity. }
            rewrite L1Form in G3. simpl in G3. apply G3 with (n := S (n - length l0)).
Qed.

Lemma beta_subset_beta_star : forall (M N : lambda_term), M ->b N -> M ->b* N.
Proof. intros M N H. unfold beta_star. unfold refl_trans_closure. exists [M;N].
       simpl. split.
  - reflexivity.
  - split.
    + reflexivity.
    + intro n. destruct n as [|n'].
      * apply H.
      * destruct n' as [|n''].
        -- reflexivity.
        -- destruct (match n'' with | 0 | _ => None end).
          ++ reflexivity.
          ++ reflexivity.
Qed.

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

(* MAIN PROOF *)
(* false, fresh variables needed... *)
Lemma lmlc_substitution : forall (M N : ml_term) (x : var),
                          lmlc (ml_substitution M N x) = substitution (lmlc M) (lmlc N) x.
Proof. induction M as [ x | M1 IHappl1 M2 IHappl2 | x M' IHfunbody| f x M' IHfixfunbody
                      | M1 IHplus1 M2 IHplus2 | M1 IHminus1 M2 IHminus2 | M1 IHtimes1 M2 IHtimes2 | n
                      | M' IHgtz
                      | | | C IHifc T IHift E IHife
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
  - intros N y. destruct (y =? f) eqn:eq_y_f.
    + destruct (y =? x) eqn:eq_y_x.
      * simpl. rewrite eq_y_f. rewrite eq_y_x. reflexivity.
      * simpl. rewrite eq_y_x. rewrite eq_y_f. simpl. destruct (y =? 0) eqn:eq_y_0.
        -- destruct (y =? 1) eqn:eq_y_1.
          ++ simpl. reflexivity.
          ++ simpl. reflexivity.
       -- destruct (y =? 1) eqn:eq_y_1.
          ++ simpl. reflexivity.
          ++ simpl. reflexivity.
    + destruct (y =? x) eqn:eq_y_x.
      * simpl. rewrite eq_y_f. rewrite eq_y_x. reflexivity.
      * simpl. rewrite eq_y_x. rewrite eq_y_f. simpl. destruct (y =? 0) eqn:eq_y_0.
        -- destruct (y =? 1) eqn:eq_y_1.
          ++ simpl. rewrite IHfixfunbody. reflexivity.
          ++ simpl. rewrite IHfixfunbody. reflexivity.
       -- destruct (y =? 1) eqn:eq_y_1.
          ++ simpl. rewrite IHfixfunbody. reflexivity.
          ++ simpl. rewrite IHfixfunbody. reflexivity.
(* M = M1 + M2 *)
  - intros N y. simpl. rewrite IHplus1. rewrite IHplus2. destruct (y =? fresh (fvL (lmlc M1) ++ fvL (lmlc M2))) eqn:eq_y_0.
        -- destruct (y =? fresh ((fresh (fvL (lmlc M1) ++ fvL (lmlc M2)))::(fvL (lmlc M1) ++ fvL (lmlc M2)))) eqn:eq_y_1.
          ++ simpl. unfold church_plus. reflexivity.
          ++ simpl. reflexivity.
       -- destruct (y =? 1) eqn:eq_y_1.
          ++ simpl. reflexivity.
          ++ simpl. reflexivity.
(* M = M1 - M2 *)
  -
(* M = M1 * M2 *)
  -
(* M = n [in NN] *)
  -
(* M = 0 < M *)
  -
(* M = true *)
  -
(* M = false *)
  -
(* M = If C then T else E *)
  -
(* M = HD::TL *)
  -
(* M = [] *)
  -
(* M = Fold_right LST OP INIT *)
  -
(* M = <P1,P2> *)
  -
(* M = fst P *)
(* M = snd P *)
Admitted.

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
Proof. induction M as [ x | M1 IHappl1 M2 IHappl2 | x M' IHfunbody| f x M' IHfixfunbody
                      | M1 IHplus1 M2 IHplus2 | M1 IHminus1 M2 IHminus2 | M1 IHtimes1 M2 IHtimes2 | n
                      | M' IHgtz
                      | | | C IHifc T IHift E IHife
                      | HD IHconshd TL IHconsnil| |LST IHfoldlst OP IHfoldop INIT IHfoldinit
                      | P1 IHpair1 P2 IHpair2 | P IHfst | P IHsnd ].
(* M = x *)
  - intros N H. simpl in H. exfalso. apply H.
(* M = (M1)M2 *)
  - intros N H. simpl. simpl in H. destruct M1 as 
                                                  [ y | L1 L2 | y L | g y L
                                                  | L1 L2 | L1 L2 | L1 L2 | m
                                                  | L
                                                  | | | C' T' E'
                                                  | HD' TL' | | LST' OP' INIT'
                                                  | P1' P2' | P' | P' ].
    (* M1 = y *)
    + simpl. simpl in H. destruct N. all : try (exfalso; apply H).
      * simpl. destruct H.
        ++ exfalso. apply H.
        ++ destruct H as [H1 H2]. rewrite <- H1. simpl. apply IHappl2 in H2.
           apply beta_star_contextual_appl'r. apply H2.
    (* M1 = (L1)L2 *)
    + destruct N. all : try (exfalso ; apply H).
      * destruct H.
        ++ destruct H. apply IHappl1 in H. simpl. rewrite H0.
           apply beta_star_contextual_appl'l. simpl in H. apply H.
        ++ destruct H. rewrite H. simpl. apply beta_star_contextual_appl'r. apply IHappl2. apply H0.
    (* M1 = fun y -> L *)    
    + destruct N as 
                  [ z | T1 T2 | z T | h z T
                  | T1 T2 | T1 T2 | T1 T2 | m
                  | T
                  | | | C'' T'' E''
                  | HD'' TL'' | | LST'' OP'' INIT''
                  | P1'' P2'' | P'' | P'' ].
      * simpl. 
(* M = fun x -> M' *)
  -
(* M = fixfun f x -> M' *)
  -
(* M = M1 + M2 *)
  -
(* M = M1 - M2 *)
  -
(* M = M1 * M2 *)
  -
(* M = n [in NN] *)
  -
(* M = 0 < M *)
  -
(* M = true *)
  -
(* M = false *)
  -
(* M = If C then T else E *)
  -
(* M = HD::TL *)
  -
(* M = [] *)
  -
(* M = Fold_right LST OP INIT *)
  -
(* M = <P1,P2> *)
  -
(* M = fst P *)
(* M = snd P *)

