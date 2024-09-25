type 'a var = unit

type _ typed_term =
  | Var : ('a var) -> ((('x -> 'a)->'gtl) * 'a) typed_term
  | Appl : (('g * ('a -> 'b)) typed_term * ('g * 'a) typed_term) -> ('g * 'b) typed_term
  | Labs : ((('x -> 'a) -> 'g_tl) * 'b typed_term) -> ('g_tl * ('a -> 'b)) typed_term
  | PermContext : ('g_tl * 'b) typed_term -> (('l -> 'g_tl) * 'b) typed_term

type raw_term = 
  | RVar of string
  | RAppl of (raw_term * raw_term)
  | RLabs of (raw_term)

let rec raw_to_typed : raw_term -> _ typed_term = fun _P ->
  try match _P with
    | RVar x -> Var ()
    | RAppl (_M, _N) -> Appl (raw_to_typed _M, raw_to_typed _N)
    | RLabs _M -> Labs (raw_to_typed _M)
  with
    | _ -> PermContext (raw_to_typed _P)