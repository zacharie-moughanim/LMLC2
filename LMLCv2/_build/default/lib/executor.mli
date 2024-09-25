open Lang

type substitution
val eval : lambda_var -> substitution -> lambda_term option
val add : lambda_var -> lambda_term -> substitution -> substitution
val remove_tail_rec : lambda_var -> substitution -> substitution -> substitution
val remove : lambda_var -> substitution -> substitution

val rename_var : lambda_var -> lambda_var -> lambda_term -> lambda_term
val evaluate : lambda_term -> lambda_term