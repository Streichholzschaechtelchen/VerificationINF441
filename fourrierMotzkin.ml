open Simplex

(*Workaround : no Array.map2 for OCaml < 4.03*)
       
let array_map2 f a1 a2 =
  Array.of_list (List.map2 f (Array.to_list a1) (Array.to_list a2))

(*Fourrier_Motzkin algorithm*)

let normalize var_count var expr positive =
  let coeff = Fraction.opp (Fraction.inv expr.(var))				  
  in Array.map (Fraction.prod coeff) expr

let substract expr1 expr2 =
  array_map2 (Fraction.sub) expr1 expr2

let rec split var_count var = function
    []
      -> [], [], []
    | expr::t when Fraction.eq expr.(var) (Fraction.foi 0)
      -> let a, b, c = split var_count var t in
	 a, b, expr::c
    | expr::t when Fraction.geq expr.(var) (Fraction.foi 0)
      -> let a, b, c = split var_count var t in
	 (normalize var_count var expr true)::a, b, c
    | expr::t
      -> let a, b, c = split var_count var t in
	 a, (normalize var_count var expr false)::b, c

let fourrier_motzkin var_count inv var =
  let a, b, c = split var_count var (List.map snd inv) in
  let rec aux1 acc h = function
      []   -> acc
    | k::t -> aux1 ((substract k h)::acc) h t
  in
  let rec aux0 acc = function
      []   -> acc
    | h::t -> aux0 (aux1 acc h b) t
  in
  let s_new_inv = aux0 [] a in
  if inv = [] then []
  else let f_new_inv = fst (List.hd inv) in
       (List.map (fun x -> f_new_inv, x) (c@s_new_inv))
		(*ajouter tous les élts de inv qui ne font pas intervenir var*)
