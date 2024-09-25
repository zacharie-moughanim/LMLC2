(* SOURCE LANGUAGE *)

type 'a ml_var

type _ ml_term =
  | Var : 'a ml_var -> 'a ml_term
  | Appl : (('a -> 'b) ml_term * 'a ml_term) -> 'b ml_term
  | Fun : ('a ml_var * 'b ml_term) -> ('a->'b) ml_term
  | Plus : (int ml_term * int ml_term) -> int ml_term
  | Minus : (int ml_term * int ml_term) -> int ml_term
  | Times : (int ml_term * int ml_term) -> int ml_term
  | Int : int -> int ml_term
  | Lt : (int ml_term * int ml_term) -> bool ml_term
  | True : bool ml_term
  | False : bool ml_term
  | And : (bool ml_term * bool ml_term) -> bool ml_term
  | Or : (bool ml_term * bool ml_term) -> bool ml_term
  | If : (bool ml_term * 'a ml_term * 'a ml_term) -> 'a ml_term
  | Cons : ('a ml_term * ('a list) ml_term) -> ('a list) ml_term
  | Nil : ('a list) ml_term
  | Fold_right : (('a list) ml_term * ('a -> 'b -> 'b) ml_term * 'b ml_term) -> 'b ml_term
  | Pair : ('a ml_term * 'b ml_term) -> ('a * 'b) ml_term 
  | Fst : ('a * 'b) ml_term -> 'a ml_term
  | Snd : ('a * 'b) ml_term -> 'b ml_term

val fresh_ml : unit -> 'a ml_var

(* OBJECT LANGUAGE *)

type lambda_var
val fresh : unit -> lambda_var
type lambda_term =
  | Lvar : lambda_var -> lambda_term
  | Labs : (lambda_var * lambda_term) -> lambda_term
  | Lappl : lambda_term * lambda_term -> lambda_term
(* Basic terms constructors *)
(* predefined variables *)
val lvar_op : lambda_var
val lvar_init : lambda_var
val lvar_fst : lambda_var
val lvar_snd : lambda_var
val lvar_pair : lambda_var
(* Boolean *)
val church_true : lambda_term
val church_false : lambda_term
val church_if : lambda_term -> lambda_term -> lambda_term -> lambda_term
val church_and : lambda_term -> lambda_term -> lambda_term
val church_or : lambda_term -> lambda_term -> lambda_term
(* Integer *)
val church_int_free : int -> lambda_term
val church_int : int -> lambda_term
val church_plus : lambda_term -> lambda_term -> lambda_term
val church_minus : lambda_term -> lambda_term -> lambda_term
val church_times : lambda_term -> lambda_term -> lambda_term
val church_gtz : lambda_term -> lambda_term
(* Lambda variables/Caml variables translation *)
val lambda_of_ml : 'a ml_var -> lambda_var

val pp_lambda : lambda_term -> unit