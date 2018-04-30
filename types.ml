type var = string
  and block = (inv list) * (instr list)
  and instr = Assignment of var * expr | If of inv * block * block | While of inv * block
  and ineq = expr
  and expr = (var option * int) list
  and inv = ineq list
  and prog = var list * block
