From LMLCProof Require Import Source Object.

Fixpoint lmlc (M : ml_term) : lambda_term := match M with
  | Var x => Lvar x
  | Appl M N => Lappl (lmlc M) (lmlc N)
  | Fun x M => Labs x (lmlc M)
  | Fixfun f x M => Labs x (turing_fixpoint_applied (lmlc M))
  | Plus M N => church_plus (lmlc M) (lmlc N)
  | Minus M N => church_minus (lmlc M) (lmlc N)
  | Times M N => church_times (lmlc M) (lmlc N)
  | Int n => church_int n
  | Gtz M => church_gtz (lmlc M)
  | BoolTrue => church_true
  | BoolFalse => church_false
  | If C T E => church_if (lmlc C) (lmlc T) (lmlc E)
  | Cons HD TL => Labs 0 (Labs 1 (Lappl (Lappl (Lvar 0) (lmlc HD)) (Lappl (Lappl (lmlc TL) (Lvar 0)) (Lvar 1))))
  | Fold_right lst foo acc => Lappl (Lappl (lmlc lst) (lmlc foo)) (lmlc acc)
  | Nil => Labs 0 (Labs (1) (Lvar 1))
  | Pair P1 P2 => Labs 3 (Lappl (Lappl (Lvar 3) (lmlc P1)) (lmlc P2))
  | Fst M => Lappl (lmlc M) (Labs 1 (Labs (2) (Lvar 1)))
  | Snd M => Lappl (lmlc M) (Labs 1 (Labs (2) (Lvar 2)))
end.