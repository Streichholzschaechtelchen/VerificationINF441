type pvar = string
  and pblock = (pinv list) * (pinstr list)
  and pinstr = PAssignment of pvar * pexpr | PIf of pinv * pblock * pblock | PWhile of pinv * pblock
  and pineq = pexpr
  and pexpr = (pvar option * int) list
  and pinv = Naught of int | PUnsat of int | Expr of int * pineq | Not of int * pinv | And of int * pinv list | Or of int * pinv list
  and pprog = pvar list * pblock

type var = int
 and block = (extended_inv list * instr list)
 and instr = Assignment of var * expr | If of extended_inv * block * block | While of extended_inv * block
 and ineq = expr
 and expr = Simplex.Fraction.frac array
 and inv = int * expr list list
 and extended_inv = |Unsat of int |Inv of inv
 and prog = int * block
