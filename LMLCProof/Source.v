From LMLCProof Require Import Utils.
Require Import PeanoNat.

Definition var : Type := nat.

Inductive ml_term_gen : Type :=
  | GLet (x : var) (M : ml_term_gen) (N : ml_term_gen)
  | GLetRec (f : var) (M : ml_term_gen) (x : var) (N : ml_term_gen)
  | GVar (x : var)
  | GAppl (f : ml_term_gen) (arg : ml_term_gen)
  | GFun (x : var) (M : ml_term_gen)
  | GPlus (n : ml_term_gen) (m : ml_term_gen)
  | GMinus (n : ml_term_gen) (m : ml_term_gen)
  | GTimes (n : ml_term_gen) (m : ml_term_gen)
  | GInt (n : nat)
  | GLt (n : ml_term_gen) (m : ml_term_gen)
  | GTrue
  | GFalse
  | GAnd (b1 : ml_term_gen) (b2 : ml_term_gen)
  | GOr (b1 : ml_term_gen) (b2 : ml_term_gen)
  | GIf (cond : ml_term_gen) (brancht : ml_term_gen) (branche : ml_term_gen)
  | GCons (hd : ml_term_gen) (tl : ml_term_gen)
  | GNil
  | GFold_right (lst : ml_term_gen) (foo : ml_term_gen) (init : ml_term_gen)
  | GPair (p1 : ml_term_gen) (p2 : ml_term_gen)
  | GFst (p : ml_term_gen)
  | GSnd (p : ml_term_gen).

Inductive ml_term : Type :=
  | Var (x : var)
  | Appl (F : ml_term) (ARG : ml_term)
  | Fun (x : var) (M : ml_term)
  | Fixfun (f : var) (x : var) (M : ml_term)
  | Plus (N : ml_term) (M : ml_term)
  | Minus (N : ml_term) (M : ml_term)
  | Times (N : ml_term) (M : ml_term)
  | Int (n : nat)
  | Gtz (N : ml_term)
  | BoolTrue
  | BoolFalse
  | If (cond : ml_term) (brancht : ml_term) (branche : ml_term)
  | Cons (hd : ml_term) (tl : ml_term)
  | Nil
  | Fold_right (lst : ml_term) (foo : ml_term) (init : ml_term)
  | Pair (p1 : ml_term) (p2 : ml_term)
  | Fst (p : ml_term)
  | Snd (p : ml_term).

Fixpoint ml_substitution (M N : ml_term) (x : var) : ml_term := match M with
  | Var y => if x =? y then N else Var y
  | Appl f arg => Appl (ml_substitution f N x) (ml_substitution arg N x)
  | Fun y M' => if x =? y then Fun y M' else Fun y (ml_substitution M' N x)
  | Fixfun f y M' => if x =? f then Fixfun f y M'
                     else if x =? y then  Fixfun f y M'
                     else Fixfun f y (ml_substitution M' N x)
  | Plus M' N' => Plus (ml_substitution M' N x) (ml_substitution N' N x)
  | Minus M' N' => Minus (ml_substitution M' N x) (ml_substitution N' N x)
  | Times M' N' => Times (ml_substitution M' N x) (ml_substitution N' N x)
  | Int n => Int n
  | Gtz N' => Gtz (ml_substitution N' N x)
  | BoolTrue => BoolTrue
  | BoolFalse => BoolFalse
  | If C T E => If (ml_substitution C N x) (ml_substitution T N x) (ml_substitution E N x)
  | Cons HD TL => Cons (ml_substitution HD N x) (ml_substitution TL N x)
  | Nil => Nil
  | Fold_right LST OP INIT => Fold_right (ml_substitution LST N x) (ml_substitution OP N x) (ml_substitution INIT N x)
  | Pair P1 P2 => Pair (ml_substitution P1 N x) (ml_substitution P2 N x)
  | Fst P => Fst (ml_substitution P N x)
  | Snd P => Snd (ml_substitution P N x)
end.

Fixpoint fvML (M : ml_term) : list var := match M with
  | Var x => [x]
  | Appl M' N' => fvML M' ++ fvML N'
  | Fun x M' => remove_nat (fvML M') x
  | Fixfun f x M' => remove_nat (remove_nat (fvML M') f) x
  | Plus M' N' => fvML M' ++ fvML N'
  | Minus M' N' => fvML M' ++ fvML N'
  | Times M' N' => fvML M' ++ fvML N'
  | Int n => []
  | Gtz N' => fvML N'
  | BoolTrue => []
  | BoolFalse => []
  | If C T E => fvML C ++ fvML T ++ fvML E
  | Cons HD TL => fvML HD ++ fvML TL
  | Nil => []
  | Fold_right LST OP INIT => fvML LST ++ fvML OP ++ fvML INIT
  | Pair P1 P2 => fvML P1 ++ fvML P2
  | Fst P => fvML P
  | Snd P => fvML P
end.


Fixpoint ml_reduction (M0 N0 : ml_term) : Prop := match M0, N0 with
(* context cases *)
  | Fun x M', Fun y N' => x = y /\ ml_reduction M' N'
  | Fixfun f x M', Fixfun g y N' => x = y /\ f = g /\ ml_reduction M' N'
  | Appl f arg, Appl f' arg' => ml_reduction f f' /\ arg = arg' \/ f = f' /\ ml_reduction arg arg'
  | Plus M N, Plus M' N' => M = M' /\ ml_reduction N N' \/ ml_reduction M M' /\ N = N'
  | Minus M N, Minus M' N' => M = M' /\ ml_reduction N N' \/ ml_reduction M M' /\ N = N'
  | Times M N, Times M' N' => M = M' /\ ml_reduction N N' \/ ml_reduction M M' /\ N = N'
  | Gtz M, Gtz M' => ml_reduction M M'
  | If cond brancht branche, If cond' brancht' branche' =>
         cond = cond' /\ brancht = brancht' /\ ml_reduction branche branche'
      \/ cond = cond' /\ ml_reduction brancht brancht' /\ branche = branche'
      \/ ml_reduction cond cond' /\ brancht = brancht' /\ branche = branche'
  | Cons HD TL, Cons HD' TL' => HD = HD' /\ ml_reduction TL TL' \/ ml_reduction HD HD' /\ TL = TL'
  | Fold_right lst foo init, Fold_right lst' foo' init' =>
         lst = lst' /\ foo = foo' /\ ml_reduction init init'
      \/ lst = lst' /\ ml_reduction foo foo' /\ init = init'
      \/ ml_reduction lst lst' /\ foo = foo' /\ init = init'
  | Pair P1 P2, Pair Q1 Q2 => ml_reduction P1 Q1 /\ P2 = Q2 \/ P1 = Q1 /\ ml_reduction P2 Q2
  | Fst P, Fst Q => ml_reduction P Q
  | Snd P, Snd Q => ml_reduction P Q
(* beta-reduction *)
  | Appl (Fun x M) N, N' => ml_substitution M N x = N'
  | Fixfun f x M', Appl M'' N'' => M'' = (Fun f (Fun x M')) /\ N'' = (Fixfun f x M')
(* Arithmetic operations *)
  | Plus (Int n) (Int m), Int n' => n' = n + m
  | Times (Int n) (Int m), Int n' => n' = n*m
  | Minus (Int n) (Int m), Int n' => n' = n-m
(* Comparison *)
  | Gtz (Int n), BoolTrue => 0 < n
  | Gtz (Int n), BoolFalse => ~(0 < n)
(* Fold_right *)
  | Fold_right (Cons HD TL) foo init, Result => Result = Fold_right TL foo (Appl (Appl foo HD) init)
  | Fold_right Nil foo init, init' => init = init'
(* Pairs operations *)
  | Fst (Pair P1 P2), P' => P1 = P'
  | Snd (Pair P1 P2), P' => P2 = P'
  | _, _ => False
end.

Fixpoint ml_gen_to_ml (M : ml_term_gen) : ml_term := match M with
  | GVar x => Var x
  | GLet x M N => Appl (Fun x (ml_gen_to_ml N)) (ml_gen_to_ml M)
  | GLetRec f M x N => Appl (Fun f (ml_gen_to_ml N)) (Fixfun f x (ml_gen_to_ml M))
  | GAppl f arg => Appl (ml_gen_to_ml f) (ml_gen_to_ml arg)
  | GFun x M => Fun x (ml_gen_to_ml M)
  | GPlus M N => Plus (ml_gen_to_ml M) (ml_gen_to_ml N)
  | GMinus M N => Minus (ml_gen_to_ml M) (ml_gen_to_ml N)
  | GTimes M N => Times (ml_gen_to_ml M) (ml_gen_to_ml N)
  | GInt n => Int n
  | GLt M N => Gtz (Minus (ml_gen_to_ml M) (ml_gen_to_ml N))
  | GTrue => BoolTrue
  | GFalse => BoolFalse
  | GAnd M N => If (ml_gen_to_ml M) (ml_gen_to_ml N) BoolFalse
  | GOr M N => If (ml_gen_to_ml M) BoolTrue (ml_gen_to_ml N)
  | GIf Cond T E => If (ml_gen_to_ml Cond) (ml_gen_to_ml T) (ml_gen_to_ml E)
  | GCons HD TL => Cons (ml_gen_to_ml HD) (ml_gen_to_ml TL)
  | GNil => Nil
  | GFold_right LST FOO INIT => Fold_right (ml_gen_to_ml LST) (ml_gen_to_ml FOO) (ml_gen_to_ml INIT)
  | GPair P1 P2 => Pair (ml_gen_to_ml P1) (ml_gen_to_ml P2)
  | GFst P => Fst (ml_gen_to_ml P)
  | GSnd P => Snd (ml_gen_to_ml P)
end.

Lemma ml_substitution_fv : forall (M : ml_term) (N : ml_term) (x : var),
              in_list (fvML M) x = false -> ml_substitution M N x = M.
Proof. intros *. intro H. generalize dependent N. induction M as [ y | L1 IH1 L2 IH2 | y L IHfunbody'| g y L IHfixfunbody'
                                                                | L1 IH1 L2 IH2 | L1 IH1 L2 IH2 | L1 IH1 L2 IH2 | m
                                                                | L IH
                                                                | | | C' IH1 T' IH2 E' IH3
                                                                | HD' IH1 TL' IH2 | | LST' IH1 OP' IH2 INIT' IH3
                                                                | P1' IH1 P2' IH2 | P' IH | P' IH ].
  all : try (intro N; simpl; simpl in H; apply in_list_app1 in H; destruct H as [H1 H2]; apply IH1 with (N := N) in H1;
             apply IH2 with (N := N) in H2; rewrite H1; rewrite H2; reflexivity).
  all : try (simpl; intro N; apply IH with (N := N) in H; rewrite H; reflexivity).
  all : try (simpl; reflexivity).
  all : try (intro N; simpl; simpl in H; apply in_list_app1 in H; destruct H as [H1 H2];
    apply in_list_app1 in H2; destruct H2 as [H2 H3];
    apply IH1 with (N := N) in H1; apply IH2 with (N := N) in H2; apply IH3 with (N := N) in H3;
    rewrite H1; rewrite H2; rewrite H3; reflexivity).
  - intro N. simpl. simpl in H. destruct (x =? y).
    + discriminate H.
    + reflexivity.
  - simpl in H. destruct (x =? y) eqn:eqxy.
    + simpl. rewrite eqxy. intro N. reflexivity.
    + simpl. rewrite eqxy. intro N. rewrite in_remove_nat_neq in H.
      * apply IHfunbody' with (N := N) in H. rewrite H. reflexivity.
      * rewrite Nat.eqb_sym. apply eqxy.
  -  simpl in H. destruct (x =? g) eqn:eqxg.
    + simpl. rewrite eqxg. intro N. reflexivity.
    + simpl. rewrite eqxg. intro N. destruct (x =? y) eqn:eqxy.
      * reflexivity.
      * rewrite in_remove_nat_neq in H.
        -- rewrite in_remove_nat_neq in H.
          ++ apply IHfixfunbody' with (N := N) in H. rewrite H. reflexivity.
          ++ rewrite Nat.eqb_sym. apply eqxg.
        -- rewrite Nat.eqb_sym. apply eqxy.
Qed.





