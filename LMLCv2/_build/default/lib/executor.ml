module Substitution = struct
  open Lang
  type substitution = (lambda_var * lambda_term) list
  let rec eval : lambda_var -> substitution -> lambda_term option = fun x -> function
    | [] -> None
    | (y,term)::tl -> if x = y then Some term else eval x tl
  let add = fun x term sigma -> (x,term)::sigma
  let rec remove_tail_rec = fun x acc -> function
    | [] -> acc
    | (y,term)::tl -> if x = y then remove_tail_rec x acc tl else (remove_tail_rec x ((y,term)::acc) tl)
  let remove = fun x sigma -> remove_tail_rec x [] sigma
end

open Lang
include Substitution

let rec rename_var : lambda_var -> lambda_var -> lambda_term -> lambda_term = fun x y -> function
  | Lvar z -> if x = z then Lvar y else Lvar z
  | Labs (z, _M) -> if x = z then Labs (z, _M) else Labs (z, rename_var x y _M)
  | Lappl (_M, _N) -> Lappl (rename_var x y _M, rename_var x y _N)

let rec evaluate_aux : substitution -> lambda_term -> lambda_term = fun sigma -> function
  | Lvar x -> begin match eval x sigma with
      | None -> Lvar x
      | Some term -> evaluate_aux sigma term
    end
  | Labs (x, _M) -> Labs (x, evaluate_aux (remove x sigma) _M)
  | Lappl (Labs (x, _M), _N) -> evaluate_aux (add x (rename_var x (fresh ()) _N) sigma) _M
  | Lappl (_M, _N) -> let _M' = evaluate_aux sigma _M in evaluate_aux sigma (Lappl (_M', _N))

let evaluate = fun _M -> evaluate_aux [] _M