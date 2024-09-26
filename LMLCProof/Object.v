From LMLCProof Require Import Utils Source.

Inductive lambda_term : Type :=
  | Lvar (x : var)
  | Lappl (f : lambda_term) (arg : lambda_term)
  | Labs (x : var) (M : lambda_term).

Fixpoint substitution (M N : lambda_term) (x : var) : lambda_term := match M with
  | Lvar y => if eqb x y then N else Lvar y
  | Labs y M' => if eqb x y then Labs y M' else Labs x (substitution M' N x)
  | Lappl M' N' => Lappl (substitution M' N x) (substitution M' N x)
end.

Fixpoint beta_reduction (M N : lambda_term) : Prop := match M,N with
  | Labs x M', Labs y N' => x = y /\ beta_reduction M' N'
  | Lappl f arg, Lappl f' arg' => beta_reduction f f' /\ arg = arg' \/ f = f' /\ beta_reduction arg arg'
  | Lappl (Labs x M) N, N' => substitution M N x = N'
  | _, _ => False
end.

Definition refl_trans_closure {X : Type} (R : X -> X -> Prop) : X -> X -> Prop := fun x y =>
  exists (l : list X), find_opt l 0 = Some x
                    /\ find_opt l ((length l) - 1) = Some y
                    /\ forall (n : nat), match find_opt l n, find_opt l (S n) with
                          | Some a, Some b => R a b
                          | _, _ => True
                        end
.

Definition beta_star := refl_trans_closure beta_reduction.
Definition ml_red_star := refl_trans_closure ml_reduction.
Notation "M ->b N" := (beta_reduction M N) (at level 50).
Notation "M ->ml N" := (ml_reduction M N) (at level 50).

Notation "M ->b* N" := (beta_star M N) (at level 50).
Notation "M ->ml* N" := (ml_red_star M N) (at level 50).

(* Basic terms constructors *)

(* Boolean *)
Definition church_true := Labs 0 (Labs 1 (Lvar 0)).
Definition church_false := Labs 0 (Labs 1 (Lvar 1)).
Definition church_if (c t e : lambda_term) := Lappl (Lappl c t) e.
Definition church_and (b1 b2 : lambda_term) := church_if b1 b2 church_false.
Definition church_or (b1 b2 : lambda_term) := church_if b1 church_true b2.

(* Pairs *)

Definition church_pair (M : lambda_term) (N : lambda_term) : lambda_term :=
  Labs 0 (Lappl (Lappl (Lvar 0) M) N).
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
Definition church_pred (N : lambda_term) : lambda_term :=
  church_snd
  (Lappl (Lappl N
            (Labs 0 (Labs 1
                          (Lappl (Lappl (Lvar 1) (church_succ (church_snd (Lvar 0))))
                               (church_succ (church_snd (Lvar 0)))))))
       (church_pair (church_int 0) (church_int 0))).

Definition church_plus (M N : lambda_term) : lambda_term := Labs 1 (Labs 0 (
                                                 Lappl (Lappl N (Lvar 1))
                                                       (Lappl (Lappl M (Lvar 1))
                                                              (Lvar 0)))
                                              ).
Definition church_minus (M N : lambda_term) : lambda_term :=
      Lappl (Lappl M (Labs 0 (church_pred (Lvar 0)))) N.
Definition church_times (M N : lambda_term) : lambda_term := Labs 1 (Labs 0 (
                                                 Lappl (Lappl N (Lvar 1))
                                                       (Lappl (Lappl M (Lvar 1))
                                                              (Lvar 0)))
                                              ).
Definition church_gtz (M : lambda_term) : lambda_term := Lappl (Lappl M (Labs 0 church_true)) (church_false).

(* Turing fixpoint *)

Definition turing_fixpoint_half : lambda_term := 
                        Labs 1 (Labs 0 (Lappl (Lvar 0) (Lappl (Lappl (Lvar 1) (Lvar 1)) (Lvar 0)))).

Definition turing_fixpoint : lambda_term := Lappl turing_fixpoint_half turing_fixpoint_half.

Definition turing_fixpoint_applied (M : lambda_term) : lambda_term := Lappl M (Lappl (turing_fixpoint) M).



