(* SOURCE LANGUAGE *)

type 'a ml_var = string

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


let fresh_counter_ml = ref 0

let fresh_ml = fun _ -> incr fresh_counter_ml; "fresh_"^(string_of_int !fresh_counter_ml)

(* OBJECT LANGUAGE *)

type lambda_var = string

let fresh_counter = ref 0

let fresh : unit -> lambda_var = fun _ -> incr fresh_counter; "fresh_"^(string_of_int !fresh_counter)

type lambda_term =
  | Lvar : lambda_var -> lambda_term
  | Labs : (lambda_var * lambda_term) -> lambda_term
  | Lappl : lambda_term * lambda_term -> lambda_term

(* Basic terms constructors *)

(* Predefined variables *)
let lvar_op = "op"
let lvar_init = "init"
let lvar_fst = "fst"
let lvar_snd = "snd"
let lvar_pair = "pair"

(* Boolean *)
let church_true = Labs ("t",Labs("e", Lvar "t"))
let church_false = Labs ("t",Labs("e", Lvar "e"))
let church_if : lambda_term -> lambda_term -> lambda_term -> lambda_term = fun c t e -> Lappl(Lappl(c, t), e)
let church_and : lambda_term -> lambda_term -> lambda_term = fun m n -> church_if m n church_false
let church_or : lambda_term -> lambda_term -> lambda_term = fun m n -> church_if m church_true n

(* Integer *)
let rec church_int_free : int -> lambda_term = function
  | 0 -> Lvar "z"
  | n -> Lappl(Lvar "s", church_int_free (n-1))
let church_int : int -> lambda_term = fun n -> Labs("s", Labs("z", church_int_free n))
let church_plus : lambda_term -> lambda_term -> lambda_term = fun n m -> Labs ("s", Labs("z", Lappl(Lappl(n, Lvar "s"), Lappl(Lappl(m, Lvar "s"), Lvar "z"))))
let church_minus : lambda_term -> lambda_term -> lambda_term = fun x y -> ignore y; x (* TODO *)
let church_times : lambda_term -> lambda_term -> lambda_term = fun n m -> Labs ("s", Labs("z", Lappl(Lappl(n, Lappl(m, Lvar "s")), Lvar "z")))
let church_gtz : lambda_term -> lambda_term = fun x -> ignore x; Labs ("t",Labs("e", Lvar "t"))

(* Lambda variables/Caml variables translation *)
let lambda_of_ml : 'a ml_var -> lambda_var = fun x -> x

(* Pretty printing *)

let rec string_of_lambda = function
  | Lvar x -> x
  | Lappl (_M,_N) -> Printf.sprintf "(%s)%s" (string_of_lambda _M) (string_of_lambda _N)
  | Labs (x, _M) -> Printf.sprintf "λ %s . %s" x (string_of_lambda _M)

let pp_lambda = fun x -> print_string (string_of_lambda x); print_newline ()