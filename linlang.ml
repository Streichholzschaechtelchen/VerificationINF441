open Simplex
open FourrierMotzkin

let verifier (var_count : int) =
  object (s)

    method opp_expr : Types.expr -> Types.expr =
      Array.map Fraction.opp

    method one_expr (var : Types.var) : Types.expr -> Types.expr  =
      Array.mapi (fun i x -> if i = var then (Fraction.foi (-1)) else x)
		 
    method neg_ineq : Types.ineq -> Types.ineq =
      Array.mapi (fun i x -> if i = var_count
			     then (Fraction.sum (Fraction.opp x)
						(Fraction.foi (-1)))
			     else (Fraction.opp x))

    method and_dnf (inv1 : Types.inv) (inv2 : Types.inv) =
      let f_inv1, s_inv1 = inv1
      and f_inv2, s_inv2 = inv2 in
      let aux acc conj =
	(List.map (fun x -> x@conj) s_inv1)@acc
      in match s_inv1, s_inv2, f_inv1 with
	   [], _ , _       -> inv2
	 | _ , [], _       -> inv1
	 | _ , _ , 0       -> (f_inv2, List.fold_left aux [] s_inv2)
	 | _ , _ , _       -> (f_inv1, List.fold_left aux [] s_inv2)        
				
    method neg_dnf (inv : Types.inv) : Types.inv =
      fst inv,
      snd (List.fold_right s#and_dnf
			   (List.map (fun conj
				      -> (0,
					  List.map (fun ineq ->
						    [s#neg_ineq ineq])
						   conj
					 )
				     )
				     (snd inv)
			   )
			   (0, [])
	  )
	  
    method or_dnf (inv1 : Types.inv) (inv2 : Types.inv) : Types.inv =
      let f_inv1, s_inv1 = inv1
      and f_inv2, s_inv2 = inv2 in
      (if f_inv1 = 0 then f_inv2 else f_inv1), s_inv1@s_inv2

    method vars_from_z_to_n (expr : Types.expr) : Types.expr =
      let vars_only = Array.sub expr 0 var_count in
      Array.append vars_only (Array.map Fraction.opp vars_only)	       
		   
    (*Auxiliary functions for verification tasks*)

    method last : 'a list -> 'a option = function
	[]   -> None
      | [h]  -> Some h
      | h::t -> s#last t

    (*Verify assignment : auxiliary functions*)

    method update_expr (var : Types.var) (expr0 : Types.expr) (expr : Types.expr) : Types.expr =
      let coeff = Fraction.div expr.(var) expr0.(var) in
      Array.mapi (fun j x -> match j with
			       i when i = var -> coeff
			     | i              -> Fraction.sum x (Fraction.opp (Fraction.prod coeff expr0.(i)))
		 ) expr

    method update_inv (var : Types.var) (expr0 : Types.expr) (inv : Types.inv) : Types.inv =
      fst inv, List.map (List.map (s#update_expr var expr0)) (snd inv)


    (*Verify conj = (expr1 && expr2 && ... && exprn) => expr*)
			
    method verify_expr (conj : Types.expr list) (expr : Types.expr) : bool =
      let k = List.length conj in
      let l = 2 * var_count - 1 in
      let b = Array.of_list (expr.(var_count)::(List.map (fun x -> x.(var_count)) conj)) in
      let a = Array.of_list ((s#vars_from_z_to_n expr)::(List.map s#vars_from_z_to_n conj)) in
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
	
    method verify_inv (inv0 : Types.inv) (inv : Types.inv) : bool =
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
			  -> let lhs = snd (List.fold_left s#and_dnf
							   (f_inv0, [ineq])
							   (List.map (fun expr -> s#neg_dnf (0, [expr]))
								     (List.tl s_inv) )
					   )
			     in List.for_all (fun conj -> List.for_all (s#verify_expr conj)
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

    method simplify_conj (conj : Types.expr list) : Types.expr list =
      match conj with
	[]      -> []
      | [expr]  -> [expr]
      | expr::t -> begin let st = s#simplify_conj t in
			 if s#verify_expr st expr
			 then st
			 else expr::st
		   end
		     
    method simplify_inv (inv : Types.inv) : Types.inv =
      let finv = fst inv in
      let sinv1 = List.map s#simplify_conj (snd inv) in
      let rec aux l =
	match l with
	  []      -> []
	| [conj]  -> [conj]
	| conj::t -> begin let st = aux t in
			   if s#verify_inv (finv, [conj]) (finv, st) 
			   then st
			   else conj::st
		     end
      in fst inv, aux sinv1
		      
    (*Conversion from parsing types to (abstract) analysis types*)
		      
    method abstract_expr (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pexpr : Types.pexpr) : Types.expr =
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
	
    method abstract_inv (var_codes : (Types.pvar, Types.var) Hashtbl.t) : Types.pinv -> Types.inv  = function
	Types.Naught (i)     -> i, []
      | Types.Expr (i, pexpr)-> i, [[s#abstract_expr var_codes pexpr]]
      | Types.Not  (i, pinv) -> i, let inv = s#abstract_inv var_codes pinv
				   in snd (s#neg_dnf inv)
      | Types.And (i, pinvl) -> i, let invl = List.map (s#abstract_inv var_codes) pinvl
				   in snd (List.fold_left s#and_dnf (List.hd invl) (List.tl invl))
      | Types.Or (i, pinvl)  -> i, let invl = List.map (s#abstract_inv var_codes) pinvl
				   in snd (List.fold_right s#or_dnf (List.tl invl) (List.hd invl))

    method compute_inv_assignment (new_assignment : Types.instr) (pre : Types.inv) (post : Types.inv) : Types.inv =
      if (snd post) == []
      then begin 
	  match new_assignment with
	    Types.Assignment(var, expr) -> begin
					  if not (Fraction.eq expr.(var) (Fraction.foi 0))
					  then s#update_inv var expr pre
					  else let oned_expr = s#one_expr var expr in
					       (s#and_dnf (fst pre, [[oned_expr; s#opp_expr oned_expr]])
							(fourrier_motzkin var_count pre var))
					end
	  | _                           -> failwith "This case should never occur"
	end
      else post
	     
    method compute_inv_if (if_last_inv : Types.inv) (else_last_inv : Types.inv) (post : Types.inv) : Types.inv =
      if (snd post) == []
      then 
	let new_post_ = s#or_dnf if_last_inv else_last_inv
	in s#simplify_inv new_post_
      else post
	     
    method compute_inv_while (pre : Types.inv) (while_last_inv : Types.inv) (inv : Types.inv) (post : Types.inv) : Types.inv =
      if (snd post) == []
      then
	let new_post_ = s#and_dnf (s#neg_dnf inv) (s#or_dnf while_last_inv pre)
	in s#simplify_inv new_post_
      else post

    method last_inv_of_while : Types.instr -> Types.inv = function
	Types.While(_, b) -> begin match s#last (fst b) with
				     None   -> (0, [])
				   | Some i -> i
			     end
      | _                 -> failwith "This case should never occur"

    method last_invs_of_if : Types.instr -> Types.inv * Types.inv = function
	Types.If(_, b1, b2) -> begin
			      (match s#last (fst b1) with
				 None   -> (0, [])
			       | Some i -> i),
			      (match s#last (fst b2) with
				 None   -> (0, [])
			       | Some i -> i)
			    end
      | _                   -> failwith "This case should never occur"
					
    method abstract_assignment (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pvar : Types.pvar) (pexpr : Types.pexpr) : Types.instr =
      if Hashtbl.mem var_codes pvar
      then Types.Assignment (Hashtbl.find var_codes pvar,
			     s#abstract_expr var_codes pexpr)
      else failwith ("Variable " ^ pvar ^ " not bound")

    method abstract_if (var_codes : (Types.pvar, Types.var) Hashtbl.t)
			(inv : Types.inv) (pblock1 : Types.pblock) (pblock2 : Types.pblock) (invp1 : Types.inv) (invp2 : Types.inv) : Types.instr =
      Types.If (inv,
		s#abstract_block var_codes pblock1 invp1,
		s#abstract_block var_codes pblock2 invp2)

    method abstract_while (var_codes : (Types.pvar, Types.var) Hashtbl.t) (inv : Types.inv) (pblock : Types.pblock) : Types.instr =
      Types.While (inv,
		   s#abstract_block var_codes pblock (0, []))

    method abstract_block (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pblock : Types.pblock) invp : Types.block =
      let invs, instrs = pblock in
      let map_abstract_invs = List.map (s#abstract_inv var_codes) in
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
								  let new_assignment = s#abstract_assignment var_codes pvar pexpr in
								  let new_post = s#compute_inv_assignment new_assignment pre post in
								  let new_tinv, new_t = aux (new_post::tinv) t
								  in pre::new_tinv, new_assignment::new_t
								end
	| pre::post::tinv, (Types.PIf(pinv, pblock1, pblock2))::t -> begin
								     let inv = s#abstract_inv var_codes pinv in
								     let if_first_inv_prop = s#and_dnf pre inv
								     and else_first_inv_prop = s#and_dnf pre (s#neg_dnf inv) in
								     let new_if = s#abstract_if var_codes inv pblock1 pblock2
											      if_first_inv_prop else_first_inv_prop in
								     let if_last_inv, else_last_inv = s#last_invs_of_if new_if in
								     let new_post = s#compute_inv_if if_last_inv else_last_inv post in
								     let new_tinv, new_t = aux (new_post::tinv) t
								     in pre::new_tinv, new_if::new_t
					       			   end
	| pre::post::tinv, (Types.PWhile(pinv, pblock))::t       -> begin (*pas d'autocomplétion de hd inv*)
								    let inv = s#abstract_inv var_codes pinv in
								    let new_while = s#abstract_while var_codes inv pblock in
								    let while_last_inv = s#last_inv_of_while new_while in
								    let new_post = s#compute_inv_while pre while_last_inv inv post in
								    let new_tinv, new_t = aux (new_post::tinv) t
								    in pre::new_tinv, new_while::new_t
					       			  end
	| _                                                      -> failwith "This case should never occur either"
      in aux new_invs instrs

    method abstract_prog (pprog : Types.pprog) : Types.prog =
      (*create the hashtable encoding variable indices*)
      let var_codes = Hashtbl.create 10 in
      let pvars, pblock = pprog in
      List.iteri (fun i v -> if Hashtbl.mem var_codes v
			     then failwith ("Duplicate variable " ^ v)
			     else Hashtbl.add var_codes v i)
		 pvars;
      (*convert pprog to prog*)
      var_count, s#abstract_block var_codes pblock (0, [])
			 
    (*Verify assignment*)

    method verify_assignment (pre : Types.inv) (var : Types.var) (expr : Types.expr) (post : Types.inv) : bool =
      if not (Fraction.eq expr.(var) (Fraction.foi 0))
      then (*cas d'une affectation inversible*)
	s#verify_inv (s#update_inv var expr pre) post
      else (*cas d'une affectation non inversible*)
	let oned_expr = s#one_expr var expr in
	s#verify_inv (s#and_dnf (0, [[oned_expr; s#opp_expr oned_expr]]) (fourrier_motzkin var_count pre var)) post
		   
    (*Verify if statement*)

    method verify_if (pre : Types.inv) (inv : Types.inv) (block1 : Types.block) (block2 : Types.block) (post : Types.inv) : bool =
      (match s#last (fst block1) with
	 Some if_end_inv -> let if_beg_inv = List.hd (fst block1) in
			    (s#verify_inv (s#and_dnf inv pre) if_beg_inv)
			    && (s#verify_inv if_end_inv post)
       | None            -> s#verify_inv (s#and_dnf inv pre) post)
      && (match s#last (fst block2) with
	    Some else_end_inv -> let else_beg_inv = List.hd (fst block2) in
				 (s#verify_inv (s#and_dnf pre (s#neg_dnf inv)) else_beg_inv)
				 && (s#verify_inv else_end_inv post)
	  | None              -> s#verify_inv (s#and_dnf pre (s#neg_dnf inv)) post)
      && (s#verify_block block1)
      && (s#verify_block block2)

    (*Verify while statement*)
	   
    method verify_while (pre : Types.inv) (inv : Types.inv) (block : Types.block) (post : Types.inv) : bool =
      (match s#last (fst block) with
	 Some while_end_inv -> let while_beg_inv = List.hd (fst block) in
			       (s#verify_inv (s#and_dnf inv pre) while_beg_inv)
			       && (s#verify_inv (s#and_dnf inv while_end_inv) while_beg_inv)
			       && (s#verify_inv (s#and_dnf while_end_inv (s#neg_dnf inv)) post)
       | None               -> true)
      && (s#verify_inv (s#and_dnf pre (s#neg_dnf inv)) post)
      && (s#verify_block block)

    (*Verify whole block*)
	   
    method verify_block (block : Types.block) : bool = match block with
	_, []                                                -> true
      | pre::post::tinv, (Types.Assignment (var, expr))::t   -> (s#verify_assignment pre var expr post)
								&& (s#verify_block ((post::tinv), t))
      | pre::post::tinv, (Types.If (inv, block1, block2))::t -> (s#verify_if pre inv block1 block2 post)
								&& (s#verify_block ((post::tinv), t))
      | pre::post::tinv, (Types.While (inv, block))::t       -> (s#verify_while pre inv block post)
								&& (s#verify_block ((post::tinv), t))
      | _, _                                                 -> failwith "should never reach that case"

  end

(*Main function*)
							       
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let pprog = Parser.progc Lexer.token lexbuf in
  Printer.print_pprog pprog; flush stdout;
  print_string "Completing invariants...\n";
  let var_count = List.length (fst pprog) in
  let my_verifier = verifier var_count in
  let proc = snd(my_verifier#abstract_prog pprog) in
  Printer.print_prog (var_count, proc); flush stdout;
  if my_verifier#verify_block proc
  then print_string "Verified!\n"
  else print_string "Could not be verified.\n"; 
  ()

    
