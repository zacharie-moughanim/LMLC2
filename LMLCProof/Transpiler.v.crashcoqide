From LMLCProof Require Import Utils Source Object.

Fixpoint lmlc (M : ml_term) : lambda_term := match M with
  | Var x => Lvar x
  | Appl M N => Lappl (lmlc M) (lmlc N)
  | Fun x M => Labs x (lmlc M)
  | Fixfun f x M => (turing_fixpoint_applied (Labs f (Labs x (lmlc M))))
  | Plus M N => let s := fresh ((fvML M) ++ (fvML N)) in let z := fresh [s] in church_plus (lmlc M) (lmlc N) s z
  | Minus M N => church_minus (lmlc M) (lmlc N)
  | Times M N => church_times (lmlc M) (lmlc N)
  | Int n => church_int n
  | Gtz M => church_gtz (lmlc M)
  | Bool b => if b then church_true else church_false
  | If C T E => church_if (lmlc C) (lmlc T) (lmlc E)
  | Cons HD TL => let foo := fresh ((fvML HD) ++ (fvML TL)) in
                  let init := fresh [foo] in
    Labs foo (Labs init (Lappl (Lappl (lmlc TL) (Lvar foo)) (Lappl (Lappl (Lvar foo) (lmlc HD)) (Lvar init))))
  | Fold_right lst foo acc => Lappl (Lappl (lmlc lst) (lmlc foo)) (lmlc acc)
  | Nil => Labs 0 (Labs 1 (Lvar 1))
  | Pair P1 P2 => let z := fresh (fvML P1 ++ fvML P2) in Labs z (Lappl (Lappl (Lvar z) (lmlc P1)) (lmlc P2))
  | Fst M => let x1 := fresh (fvML M) in let x2 := fresh [x1] in
                Lappl (lmlc M) (Labs x1 (Labs x2 (Lvar x1)))
  | Snd M => let x1 := fresh (fvML M) in let x2 := fresh [x1] in
                Lappl (lmlc M) (Labs x1 (Labs x2 (Lvar x2)))
end.

Lemma fvML_L : forall (M : ml_term), fvL (lmlc M) = fvML M.
Proof. induction M as [ x | M1 IHappl1 M2 IHappl2 | x M' IHfunbody| f x M' IHfixfunbody
                      | M1 IHplus1 M2 IHplus2 | M1 IHminus1 M2 IHminus2 | M1 IHtimes1 M2 IHtimes2 | n
                      | M' IHgtz
                      | | C IHifc T IHift E IHife
                      | HD IHconshd TL IHconsnil| |LST IHfoldlst OP IHfoldop INIT IHfoldinit
                      | P1 IHpair1 P2 IHpair2 | P IHfst | P IHsnd ].
  - reflexivity.
  - simpl. rewrite IHappl1. rewrite IHappl2. reflexivity.
  - simpl. rewrite IHfunbody. reflexivity.
  - simpl. rewrite IHfixfunbody. admit.
Admitted.