let assemble_inequality ?strict:(s=false) lhs rhs =
  (if s then [None, -1] else [])@lhs@(List.map (fun x -> fst x, -snd x) rhs)

let assemble_and i lhs rhs = match lhs, rhs with
    (Types.And (_, l)) , (Types.And (_, r)) -> Types.And (i, l@r)
  | (Types.And (_, l)) , _                  -> Types.And (i, rhs::l)
  | _                  , (Types.And (_, r)) -> Types.And (i, lhs::r)
  | (Types.Or (_, _))  , _                  
  | (Types.Not (_, _)) , _
  | (Types.Expr (_, _)), _
  | (Types.Naught (_)) , _                  -> Types.And (i, [lhs; rhs])

let assemble_or i lhs rhs = match lhs, rhs with
    (Types.Or (_, l))  , (Types.Or (_, r)) -> Types.Or (i, l@r)
  | (Types.Or (_, l))  , _                 -> Types.Or (i, rhs::l)
  | _                  , (Types.Or (_, r)) -> Types.Or (i, lhs::r)
  | (Types.And (_, _)) , _                  
  | (Types.Not (_, _)) , _
  | (Types.Expr (_, _)), _
  | (Types.Naught (_)) , _                 -> Types.Or (i, [lhs; rhs])

			 
