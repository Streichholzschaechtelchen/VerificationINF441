type pvar = string
  and pblock = (pinv list) * (pinstr list)
  and pinstr = PAssignment of pvar * pexpr | PIf of pinv * pblock * pblock | PWhile of pinv * pblock
  and pineq = pexpr
  and pexpr = int * (pvar option * int) list
  and pinv = pineq list
  and pprog = pvar list * pblock

type var = int
 and block = (inv list * instr list)
 and instr = Assignment of var * expr | If of inv * block * block | While of inv * block
 and ineq = expr
 and expr = int * Simplex.Fraction.frac array
 and inv = expr list
 and prog = int * block

	      
