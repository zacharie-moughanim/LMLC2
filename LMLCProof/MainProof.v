Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Definitions.

From LMLCProof Require Import Source Object Transpiler.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


(** Beta-Eeduction properties *)

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

Theorem lmlc_is_correct : forall (M N : ml_term), M ->ml N -> (lmlc M) ->b* (lmlc N).
Proof. induction M as [ x | M1 IHappl1 M2 IHappl2| x M' IHfunbody| f x M' IHfixfunbody
                      | M1 IHplus1 M2 IHplus2| M1 IHminus1 M2 IHminus2 | M1 IHtimes1 M2 IHtimes2 | n
                      | M' IHgtz
                      | | | C IHifc T IHift E IHife
                      | HD IHconshd TL IHconsnil| |LST IHfoldlst OP IHfoldop INIT IHfoldinit
                      | P1 IHpair1 P2 IHpair2 | P IHfst | P IHsnd ].
(* M = x *)
  - intros N H. simpl in H. exfalso. apply H.
(* M = (M1)M2 *)
  - intros N H. simpl. simpl in H. destruct M1 eqn:eqM1.
    + simpl. simpl in H. destruct N eqn:eqN. all : try (exfalso; apply H).
      * simpl. destruct H.
        ++ exfalso. apply H.
        ++ destruct H as [H1 H2]. rewrite <- H1. simpl. apply IHM2 in H2.
           apply beta_star_contextual_appl'r. apply H2.
    + destruct N eqn:eqN. all : try (exfalso; apply H).
      * simpl. destruct H.
        ++
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

