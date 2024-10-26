type mlToken = 
  | 
  | 
(* fun, ->, (/), [/], ::, integers, booleans, &&, ||, if, then, else, +/-/*, <, <=, >=, >, fst, snd, [,] *)
val lexer : string -> mlToken list