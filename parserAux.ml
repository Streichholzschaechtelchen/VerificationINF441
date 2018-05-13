let assemble_inequality ?strict:(s=false) lhs rhs =
  (fst lhs), (if s then [None, -1] else [])@(snd lhs)@(List.map (fun x -> fst x, -snd x) (snd rhs))

			 
