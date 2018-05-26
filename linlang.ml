open Simplex
open FourrierMotzkin

(*Auxiliary functions for verification tasks*)

let rec last : 'a list -> 'a option = function
    []   -> None
  | [h]  -> Some h
  | h::t -> last t

let opp_expr : Types.expr -> Types.expr =
  Array.map Fraction.opp

let one_expr (var : Types.var) : Types.expr -> Types.expr  =
  Array.mapi (fun i x -> if i = var then (Fraction.foi (-1)) else x)

let neg_ineq (var_count : int) : Types.ineq -> Types.ineq =
  Array.mapi (fun i x -> if i = var_count
			 then (Fraction.sum (Fraction.opp x)
					    (Fraction.foi (-1)))
			 else (Fraction.opp x))

let vars_from_z_to_n (var_count : int) (expr : Types.expr) : Types.expr =
  let vars_only = Array.sub expr 0 var_count in
  Array.append vars_only (Array.map Fraction.opp vars_only)

(*Verify conj = (expr1 && expr2 && ... && exprn) => expr*)
			    
let verify_expr (var_count : int) (conj : Types.expr list) (expr : Types.expr) : bool =
  let k = List.length conj in
  let l = 2 * var_count - 1 in
  let b = Array.of_list (expr.(var_count)::(List.map (fun x -> x.(var_count)) conj)) in
  let a = Array.of_list ((vars_from_z_to_n var_count expr)::(List.map (vars_from_z_to_n var_count) conj)) in
  print_string "Verifying conjunction ";
  Printer.print_inv var_count (0, [conj]);
  print_string " => ";
  Printer.print_inv var_count (0, [[expr]]);
  print_newline ();
  print_string "Sending k:\n"; print_int k; print_newline ();
  print_string "Sending l:\n"; print_int l; print_newline ();
  print_string "Sending a:\n"; print_matrix a;
  print_string "Sending b:\n"; print_array b;
  print_newline ();
  let simplex_min = simplex a b k l in
  let result = Fraction.geq simplex_min (Fraction.foi 0) in
  if result
  then begin print_string "OK, minimum is ";
	     Fraction.print_frac simplex_min;
	     print_newline ()
       end
  else begin print_string "Failed, minimum is ";
	     Fraction.print_frac simplex_min;
	     print_newline ()
       end;
  result

(*Verify conj0 => conj*)
    
let and_dnf (var_count : int) (inv1 : Types.inv) (inv2 : Types.inv) =
  let f_inv1, s_inv1 = inv1
  and f_inv2, s_inv2 = inv2 in
  let aux acc conj =
    (List.map (fun x -> x@conj) s_inv1)@acc
  in match s_inv1, s_inv2, f_inv1 with
       [], _ , _       -> inv2
     | _ , [], _       -> inv1
     | _ , _ , 0       -> (f_inv2, List.fold_left aux [] s_inv2)
     | _ , _ , _       -> (f_inv1, List.fold_left aux [] s_inv2)        

let neg_dnf (var_count : int) (inv : Types.inv) : Types.inv =
  fst inv,
  snd (List.fold_right (and_dnf var_count)
		       (List.map (fun conj
				  -> (0,
				      List.map (fun ineq ->
						[neg_ineq var_count
							  ineq])
					       conj
				     )
				 )
				 (snd inv)
		       )
		       (0, [])
      )

let or_dnf (var_count : int) (inv1 : Types.inv) (inv2 : Types.inv) : Types.inv =
  let f_inv1, s_inv1 = inv1
  and f_inv2, s_inv2 = inv2 in
  (if f_inv1 = 0 then f_inv2 else f_inv1), s_inv1@s_inv2
    
let verify_inv (var_count : int) (inv0 : Types.inv) (inv : Types.inv) : bool =
  let print_implication () =
    Printer.print_inv var_count inv0;
    print_string " => ";
    Printer.print_inv var_count inv;
  in
  let f_inv0, s_inv0 = inv0
  and f_inv, s_inv = inv in
  print_string "Verifying ";
  print_implication ();
  print_newline ();
  if s_inv = []
  then true
  else
    let result
      = List.for_all (fun ineq
		      -> let lhs = snd (List.fold_left (and_dnf var_count)
						       (f_inv0, [ineq])
						       (List.map (fun expr -> neg_dnf var_count (0, [expr]))
								 (List.tl s_inv) )
				       )
			 in List.for_all (fun conj -> List.for_all (verify_expr var_count conj)
								   (List.hd s_inv) )
					 lhs
		     )
		     s_inv0
    in
    begin
      if result then begin
		    print_string "Successfully verified ";
		    print_implication ();
		    print_newline ()
		  end
      else begin
	  print_string "Failed to verify ";
	  print_implication ();
	  print_newline ()
	end;
      result
    end	     

(*Simplify invariant*)

let rec simplify_conj (var_count : int) (conj : Types.expr list) : Types.expr list =
  match conj with
    []      -> []
  | [expr]  -> [expr]
  | expr::t -> begin let st = simplify_conj var_count t in
		     if verify_expr var_count st expr
		     then st
		     else expr::st
	       end
      
let simplify_inv (var_count : int) (inv : Types.inv) : Types.inv =
  let finv = fst inv in
  let sinv1 = List.map (simplify_conj var_count) (snd inv) in
  let rec aux l =
    match l with
      []      -> []
    | [conj]  -> [conj]
    | conj::t -> begin let st = aux t in
		       if List.for_all (fun x -> verify_inv var_count (finv, [x]) (finv, [conj]))
				       st
		       then st
		       else conj::st
		 end
  in fst inv, aux sinv1
		    
(*Conversion from parsing types to (abstract) analysis types*)
       
let abstract_expr (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pexpr : Types.pexpr) : Types.expr =
  let expr = Array.make (var_count + 1) (Fraction.foi 0) in
  List.iter (fun x -> match x with
			None,   i -> expr.(var_count) <- Fraction.sum expr.(var_count) (Fraction.foi i)
		      | Some v, i -> begin
				     if Hashtbl.mem var_codes v
				     then expr.(Hashtbl.find var_codes v)
					  <- Fraction.sum expr.(Hashtbl.find var_codes v) (Fraction.foi i)
				     else failwith ("Variable " ^ v ^ " not bound")
				   end
	    )
	    pexpr;
  expr
    
let rec abstract_inv (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t) : Types.pinv -> Types.inv  = function
    Types.Naught (i)     -> i, []
  | Types.Expr (i, pexpr)-> i, [[abstract_expr var_count var_codes pexpr]]
  | Types.Not  (i, pinv) -> i, let inv = abstract_inv var_count var_codes pinv
			       in snd (neg_dnf var_count inv)
  | Types.And (i, pinvl) -> i, let invl = List.map (abstract_inv var_count var_codes) pinvl
			       in snd (List.fold_left (and_dnf var_count)
						      (List.hd invl) (List.tl invl))
  | Types.Or (i, pinvl)  -> i, let invl = List.map (abstract_inv var_count var_codes) pinvl
			       in snd (List.fold_right (or_dnf var_count)
						       (List.tl invl) (List.hd invl))

let compute_inv_assignment var_count new_assignment pre post =
  if (snd post) == []
  then begin 
      match new_assignment with
	Types.Assignment(var, expr) -> let oned_expr = one_expr var expr in
				       let new_post_ = and_dnf var_count
							       (fst post, snd pre)
							       (fst post, [[opp_expr oned_expr; oned_expr]])
				       in simplify_inv var_count new_post_
      | _                           -> failwith "This case should never occur"
    end
  else post
						
let compute_inv_if var_count if_last_inv else_last_inv post =
  if (snd post) == []
  then 
    let new_post_ = or_dnf var_count if_last_inv else_last_inv
    in simplify_inv var_count new_post_
  else post
	 
let compute_inv_while var_count pre while_last_inv inv post =
  if (snd post) == []
  then
    let new_post_ = or_dnf var_count (and_dnf var_count while_last_inv (neg_dnf var_count inv))
			   (and_dnf var_count pre (neg_dnf var_count inv))
    in simplify_inv var_count new_post_
  else post

let last_inv_of_while = function
    Types.While(_, b) -> begin match last (fst b) with
				 None   -> (0, [])
			       | Some i -> i
			 end
  | _                 -> failwith "This case should never occur"

let last_invs_of_if = function
    Types.If(_, b1, b2) -> begin
			  (match last (fst b1) with
			     None   -> (0, [])
			   | Some i -> i),
			  (match last (fst b2) with
			     None   -> (0, [])
			   | Some i -> i)
			end
  | _                   -> failwith "This case should never occur"
		  
let abstract_assignment (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pvar : Types.pvar) (pexpr : Types.pexpr) : Types.instr =
   if Hashtbl.mem var_codes pvar
   then Types.Assignment (Hashtbl.find var_codes pvar,
			  abstract_expr var_count var_codes pexpr)
   else failwith ("Variable " ^ pvar ^ " not bound")

let rec abstract_if (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t)
                    (inv : Types.inv) (pblock1 : Types.pblock) (pblock2 : Types.pblock) (invp1 : Types.inv) (invp2 : Types.inv) : Types.instr =
   Types.If (inv,
	     abstract_block var_count var_codes pblock1 invp1,
	     abstract_block var_count var_codes pblock2 invp2)

and abstract_while (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t) (inv : Types.inv) (pblock : Types.pblock) : Types.instr =
  Types.While (inv,
	       abstract_block var_count var_codes pblock (0, []))

and abstract_block (var_count : int) (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pblock : Types.pblock) invp : Types.block =
  let invs, instrs = pblock in
  let map_abstract_invs = List.map (abstract_inv var_count var_codes) in
  let new_invs_ = match map_abstract_invs invs with
      []         -> []
    | (i, [])::t -> (i, snd invp)::t
    | l          -> l
  in
  let new_invs = if List.length new_invs_ <> (List.length instrs) + 1
		 then new_invs_@[(0, [])]
		 else new_invs_
  in 
  let rec aux new_invs instrs = match new_invs, instrs with
      _, []                                                -> new_invs, []
    | pre::post::tinv, (Types.PAssignment(pvar, pexpr))::t -> begin
							      let new_assignment = abstract_assignment var_count var_codes pvar pexpr in
							      let new_post = compute_inv_assignment var_count new_assignment pre post in
							      let new_tinv, new_t = aux (new_post::tinv) t
							      in pre::new_tinv, new_assignment::new_t
							    end
    | pre::post::tinv, (Types.PIf(pinv, pblock1, pblock2))::t -> begin
								 let inv = abstract_inv var_count var_codes pinv in
								 let if_first_inv_prop = and_dnf var_count pre inv
								 and else_first_inv_prop = and_dnf var_count pre (neg_dnf var_count inv) in
								 let new_if = abstract_if var_count var_codes inv pblock1 pblock2
											  if_first_inv_prop else_first_inv_prop in
								 let if_last_inv, else_last_inv = last_invs_of_if new_if in
								 let new_post = compute_inv_if var_count if_last_inv else_last_inv post in
								 let new_tinv, new_t = aux (new_post::tinv) t
								 in pre::new_tinv, new_if::new_t
					       		       end
    | pre::post::tinv, (Types.PWhile(pinv, pblock))::t       -> begin (*pas d'autocomplétion de hd inv*)
							      let inv = abstract_inv var_count var_codes pinv in
							      let new_while = abstract_while var_count var_codes inv pblock in
							      let while_last_inv = last_inv_of_while new_while in
							      let new_post = compute_inv_while var_count pre while_last_inv inv post in
							      let new_tinv, new_t = aux (new_post::tinv) t
							      in pre::new_tinv, new_while::new_t
					       		    end
    | _                                                      -> failwith "This case should never occur either"
  in aux new_invs instrs

let abstract_prog (pprog : Types.pprog) : Types.prog =
  (*create the hashtable encoding variable indices*)
  let var_codes = Hashtbl.create 10 in
  let pvars, pblock = pprog in
  List.iteri (fun i v -> if Hashtbl.mem var_codes v
			then failwith ("Duplicate variable " ^ v)
			else Hashtbl.add var_codes v i)
	     pvars;
  let var_count = List.length pvars in
  (*convert pprog to prog*)
  var_count, abstract_block var_count var_codes pblock (0, [])

(*Verify assignment : auxiliary functions*)

let update_expr (var_count : int) (var : Types.var) (expr0 : Types.expr) (expr : Types.expr) : Types.expr =
  let coeff = Fraction.div expr.(var) expr0.(var) in
  Array.mapi (fun j x -> match j with
			   i when i = var -> coeff
			 | i              -> Fraction.sum x (Fraction.opp (Fraction.prod coeff expr0.(i)))
	     ) expr

let update_inv (var_count : int) (var : Types.var) (expr0 : Types.expr) (inv : Types.inv) : Types.inv =
  fst inv, List.map (List.map (update_expr var_count var expr0)) (snd inv)

(*Verify assignment*)

let verify_assignment (var_count : int) (pre : Types.inv) (var : Types.var) (expr : Types.expr) (post : Types.inv) : bool =
  if not (Fraction.eq expr.(var) (Fraction.foi 0))
  then (*cas d'une affectation inversible*)
    verify_inv var_count (update_inv var_count var expr pre) post
  else (*cas d'une affectation non inversible*)
    let oned_expr = one_expr var expr in
    verify_inv var_count (and_dnf var_count (0, [[oned_expr; opp_expr oned_expr]]) (fourrier_motzkin var_count pre var)) post
	       
(*Verify if statement*)

let rec verify_if (var_count : int) (pre : Types.inv) (inv : Types.inv) (block1 : Types.block) (block2 : Types.block) (post : Types.inv) : bool =
  (match last (fst block1) with
     Some if_end_inv -> let if_beg_inv = List.hd (fst block1) in
			(verify_inv var_count (and_dnf var_count inv pre) if_beg_inv)
			&& (verify_inv var_count if_end_inv post)
   | None            -> verify_inv var_count (and_dnf var_count inv pre) post)
  && (match last (fst block2) with
	Some else_end_inv -> let else_beg_inv = List.hd (fst block2) in
			     (verify_inv var_count (and_dnf var_count pre (neg_dnf var_count inv)) else_beg_inv)
			     && (verify_inv var_count else_end_inv post)
      | None              -> verify_inv var_count (and_dnf var_count pre (neg_dnf var_count inv)) post)
  && (verify_block var_count block1)
  && (verify_block var_count block2)

(*Verify while statement*)
     
and verify_while (var_count : int) (pre : Types.inv) (inv : Types.inv) (block : Types.block) (post : Types.inv) : bool =
  (match last (fst block) with
     Some while_end_inv -> let while_beg_inv = List.hd (fst block) in
			  (verify_inv var_count (and_dnf var_count inv pre) while_beg_inv)
			  && (verify_inv var_count (and_dnf var_count inv while_end_inv) while_beg_inv)
			  && (verify_inv var_count (and_dnf var_count while_end_inv (neg_dnf var_count inv)) post)
   | None               -> true)
  && (verify_inv var_count (and_dnf var_count pre (neg_dnf var_count inv)) post)
  && (verify_block var_count block)

(*Verify whole block*)
							   
and verify_block (var_count : int) (block : Types.block) : bool = match block with
    _, []                                                -> true
  | pre::post::tinv, (Types.Assignment (var, expr))::t   -> (verify_assignment var_count pre var expr post)
							    && (verify_block var_count ((post::tinv), t))
  | pre::post::tinv, (Types.If (inv, block1, block2))::t -> (verify_if var_count pre inv block1 block2 post)
							    && (verify_block var_count ((post::tinv), t))
  | pre::post::tinv, (Types.While (inv, block))::t       -> (verify_while var_count pre inv block post)
							    && (verify_block var_count ((post::tinv), t))
  | _, _                                                 -> failwith "should never reach that case"

(*Main function*)
							       
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let pprog = Parser.progc Lexer.token lexbuf in
  Printer.print_pprog pprog; flush stdout;
  print_string "Completing invariants...\n";
  let var_count, proc = abstract_prog pprog in
  Printer.print_prog (var_count, proc); flush stdout;
  if (verify_block var_count proc)
  then print_string "Verified!\n"
  else print_string "Could not be verified.\n"; 
  ()

    
