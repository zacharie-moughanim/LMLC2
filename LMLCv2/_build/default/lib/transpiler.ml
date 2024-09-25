(** TRANSPILER *)

open Lang

let rec lmlc : type a. a ml_term -> lambda_term = function
  | Var x -> Lvar (lambda_of_ml x)
  | Appl (_M, _N) -> Lappl (lmlc _M, lmlc _N)
  | Fun (x, _M) -> Labs (lambda_of_ml x, lmlc _M)
  | Plus (_M, _N) -> church_plus (lmlc _M) (lmlc _N)
  | Minus (_M, _N) -> church_minus (lmlc _M) (lmlc _N)
  | Times (_M, _N) -> church_times (lmlc _M) (lmlc _N)
  | Int n -> church_int n
  | Lt (_M, _N) -> church_gtz (church_minus (lmlc _M) (lmlc _N))
  | True -> church_true
  | False -> church_false
  | And (_M, _N) -> church_and (lmlc _M) (lmlc _N)
  | Or (_M, _N) -> church_or (lmlc _M) (lmlc _N)
  | If (_C, _T, _E) -> church_if (lmlc _C) (lmlc _T) (lmlc _E)
  | Cons (_HD, _TL) -> Labs (lvar_op, Labs(lvar_init, Lappl(Lappl(Lvar lvar_op, lmlc _HD), Lappl(Lappl(lmlc _TL, Lvar lvar_op), Lvar lvar_init))))
  | Fold_right (lst, foo, acc) -> Lappl(Lappl(lmlc lst, lmlc foo), lmlc acc)
  | Nil -> Labs (lvar_op, Labs(lvar_init, Lvar lvar_init))
  | Pair (_P1, _P2) -> Labs(lvar_pair, Lappl(Lappl(Lvar lvar_pair, lmlc _P1), lmlc _P2))
  | Fst _M -> Lappl(lmlc _M, Labs (lvar_fst,Labs(lvar_snd, Lvar lvar_fst)))
  | Snd _M -> Lappl(lmlc _M, Labs (lvar_fst,Labs(lvar_snd, Lvar lvar_snd)))