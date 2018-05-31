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

    method and_dnf (inv1 : Types.inv) (inv2 : Types.inv) : Types.inv =
      let f_inv1, s_inv1 = inv1
      and f_inv2, s_inv2 = inv2 in
      let aux acc conj =
  (List.map (fun x -> x@conj) s_inv1)@acc
      in match s_inv1, s_inv2, f_inv1 with
     [], _ , _       -> inv2
   | _ , [], _       -> inv1
   | _ , _ , 0       -> (f_inv2, List.fold_left aux [] s_inv2)
   | _ , _ , _       -> (f_inv1, List.fold_left aux [] s_inv2)


    method extended_and_dnf (xinv1 : Types.extended_inv) (xinv2 : Types.extended_inv) : Types.extended_inv =
      match (xinv1, xinv2) with
      |Types.Unsat(_), _ -> xinv1
      |_, Types.Unsat(_) -> xinv2
      |(Types.Inv inv1, Types.Inv inv2) -> Types.Inv (s#and_dnf inv1 inv2)

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


    method extended_neg_dnf (xinv : Types.extended_inv) : Types.extended_inv =
      match xinv with
      |Types.Unsat(i) -> Types.Inv(i, [])
      |Types.Inv inv -> Types.Inv (s#neg_dnf inv)

    method or_dnf (inv1 : Types.inv) (inv2 : Types.inv) : Types.inv =
    let f_inv1, s_inv1 = inv1
    and f_inv2, s_inv2 = inv2 in
    (if f_inv1 = 0 then f_inv2 else f_inv1), s_inv1@s_inv2

    method extended_or_dnf (xinv1 : Types.extended_inv) (xinv2 : Types.extended_inv) : Types.extended_inv =
      match xinv1, xinv2 with
      |Types.Unsat(_), _ -> xinv2
      |_, Types.Unsat(_) -> xinv1
      |(Types.Inv(inv1), Types.Inv(inv2)) -> Types.Inv (s#or_dnf inv1 inv2)


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

    (* verify satisfiability of conj = (expr1 && expr2 && ... && exprn) *)

    method sat_conj (conj : Types.expr list) : bool =
      let k = List.length conj in
      let l = 2 * var_count - 1 in
      let b = Array.of_list ((Fraction.foi 0)::(List.map (fun x -> x.(var_count)) conj)) in
      let a = Array.of_list ((Array.make (l + 1) (Fraction.foi 0))::(List.map s#vars_from_z_to_n conj)) in
      print_string "Verifying satifiability \n";
      let simplex_min = simplex a b k l in
      simplex_min != Fraction.Void

    method sat_inv (inv : Types.inv) : bool =
      let _, s_inv = inv in
      List.for_all (fun ineq
          -> s#sat_conj ineq)
         s_inv

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
      print_string "Sending a:\n"; LinearOperations.print_matrix a;
      print_string "Sending b:\n"; LinearOperations.print_array b;
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

    method extended_verify_inv (xinv0 : Types.extended_inv) (xinv : Types.extended_inv) : bool =
      let print_implication () =
	Printer.print_extended_inv var_count xinv0;
	print_string " => ";
	Printer.print_extended_inv var_count xinv;
      in
      match xinv0, xinv with
      |Types.Unsat(_), _ -> true
      |Types.Inv inv0, Types.Unsat(_) when not (s#sat_inv inv0) -> true
      |_, Types.Unsat(_) -> false
      |Types.Inv inv0, Types.Inv inv ->
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
			   if s#extended_verify_inv (Types.Inv (finv, [conj])) (Types.Inv (finv, st))
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


    method abstract_inv (var_codes : (Types.pvar, Types.var) Hashtbl.t) : Types.pinv -> Types.extended_inv  = function
	Types.Naught (i)     -> Types.Inv (i, [])
      | Types.PUnsat (i) -> Types.Unsat(i)
      | Types.Expr (i, pexpr)-> Types.Inv(i, [[s#abstract_expr var_codes pexpr]])
      | Types.Not  (i, pinv) -> Types.Inv(i, let xinv = s#abstract_inv var_codes pinv
				   in match xinv with
           |Types.Unsat(_) -> []
           |Types.Inv inv -> snd (s#neg_dnf inv)
      )
      | Types.And (i, pinvl) -> begin let xinvl = List.map (s#abstract_inv var_codes) pinvl
				   in match List.fold_left s#extended_and_dnf (List.hd xinvl) (List.tl xinvl) with
           |Types.Unsat(_) -> Types.Unsat(i)
           |Types.Inv inv -> Types.Inv (i, snd inv) end
      | Types.Or (i, pinvl) -> begin let xinvl = List.map (s#abstract_inv var_codes) pinvl
				   in match List.fold_left s#extended_or_dnf (List.hd xinvl) (List.tl xinvl) with
           |Types.Unsat(_) -> Types.Unsat(i)
           |Types.Inv inv -> Types.Inv (i, snd inv) end

    method compute_inv_assignment (new_assignment : Types.instr) (xpre : Types.extended_inv) (xpost : Types.extended_inv) : Types.extended_inv =
      match xpre, xpost with
      |Types.Unsat(i), Types.Inv (_, []) -> Types.Unsat(i)
      |Types.Unsat(_), _ -> xpost
      |_, Types.Unsat(i) -> Types.Unsat(i)
      |(Types.Inv pre, Types.Inv post) ->
      if (snd post) == []
      then begin
	  match new_assignment with
	    Types.Assignment(var, expr) -> begin
					  if not (Fraction.eq expr.(var) (Fraction.foi 0))
					  then Types.Inv (s#update_inv var expr pre)
					  else let oned_expr = s#one_expr var expr in
					       Types.Inv (s#and_dnf (fst pre, [[oned_expr; s#opp_expr oned_expr]])
							(fourrier_motzkin var_count pre var))
					end
	  | _                           -> failwith "This case should never occur"
	end
      else Types.Inv post

    method compute_inv_if (xif_last_inv : Types.extended_inv) (xelse_last_inv : Types.extended_inv) (xpost : Types.extended_inv) : Types.extended_inv =
      match xpost with
      | Types.Inv (_, []) -> begin
        let xnew_post_ = s#extended_or_dnf xif_last_inv xelse_last_inv
        in match xnew_post_ with
        |Types.Unsat (_) -> xnew_post_
        |Types.Inv (new_post) -> Types.Inv (s#simplify_inv new_post) end
      |_ -> xpost

    method compute_inv_while (xpre : Types.extended_inv) (xwhile_last_inv : Types.extended_inv) (xinv : Types.extended_inv) (xpost : Types.extended_inv) : Types.extended_inv =
    match xpost with
    | Types.Inv (_, []) -> begin
      let xnew_post = s#extended_and_dnf (s#extended_neg_dnf xinv) (s#extended_or_dnf xwhile_last_inv xpre)
      in match xnew_post with
      |Types.Unsat (_) -> xnew_post
      |Types.Inv (new_post) -> Types.Inv (s#simplify_inv new_post) end
    |_ -> xpost

    method last_inv_of_while : Types.instr -> Types.extended_inv = function
	Types.While(_, b) -> begin match s#last (fst b) with
				     None   -> Types.Inv (0, [])
				   | Some i -> i
			     end
      | _                 -> failwith "This case should never occur"

    method last_invs_of_if : Types.instr -> Types.extended_inv * Types.extended_inv = function
	Types.If(_, b1, b2) -> begin
			      (match s#last (fst b1) with
				 None   -> Types.Inv (0, [])
			       | Some i -> i),
			      (match s#last (fst b2) with
				 None   -> Types.Inv (0, [])
			       | Some i -> i)
			    end
      | _                   -> failwith "This case should never occur"

    method abstract_assignment (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pvar : Types.pvar) (pexpr : Types.pexpr) : Types.instr =
      if Hashtbl.mem var_codes pvar
      then Types.Assignment (Hashtbl.find var_codes pvar,
			     s#abstract_expr var_codes pexpr)
      else failwith ("Variable " ^ pvar ^ " not bound")

    method abstract_if (var_codes : (Types.pvar, Types.var) Hashtbl.t)
			(xinv : Types.extended_inv) (pblock1 : Types.pblock) (pblock2 : Types.pblock) (xinvp1 : Types.extended_inv) (xinvp2 : Types.extended_inv) : Types.instr =
      Types.If (xinv,
		s#abstract_block var_codes pblock1 xinvp1,
		s#abstract_block var_codes pblock2 xinvp2)

    method abstract_while (var_codes : (Types.pvar, Types.var) Hashtbl.t) (xinv : Types.extended_inv) (pblock : Types.pblock) : Types.instr =
      Types.While (xinv,
		   s#abstract_block var_codes pblock (Types.Inv (0, [])))

    method abstract_block (var_codes : (Types.pvar, Types.var) Hashtbl.t) (pblock : Types.pblock) (xinvp : Types.extended_inv) : Types.block =
      let invs, instrs = pblock in
      let map_abstract_invs = List.map (s#abstract_inv var_codes) in
      let new_invs_ = match map_abstract_invs invs with
	  []         -> []
	| (Types.Inv (i, []))::t -> begin
    match xinvp with
    |Types.Unsat(_) -> Types.Unsat(i) :: t
    |Types.Inv inv -> Types.Inv((i, snd inv))::t
    end
	| l          -> l
      in
      let new_invs = if List.length new_invs_ <> (List.length instrs) + 1
		     then new_invs_@[Types.Inv (0, [])]
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
								     let if_first_inv_prop = s#extended_and_dnf pre inv
								     and else_first_inv_prop = s#extended_and_dnf pre (s#extended_neg_dnf inv) in
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
      var_count, s#abstract_block var_codes pblock (Types.Inv (0, []))

    (*Verify assignment*)

    method verify_assignment (xpre : Types.extended_inv) (var : Types.var) (expr : Types.expr) (xpost : Types.extended_inv) : bool =
      match xpre, xpost with
      |Types.Unsat(_), _ -> true
      |_, Types.Unsat(_) -> false
      |Types.Inv pre, Types.Inv post ->
      if not (Fraction.eq expr.(var) (Fraction.foi 0))
      then (*cas d'une affectation inversible*)
	s#verify_inv (s#update_inv var expr pre) post
      else (*cas d'une affectation non inversible*)
	let oned_expr = s#one_expr var expr in
	s#verify_inv (s#and_dnf (0, [[oned_expr; s#opp_expr oned_expr]]) (fourrier_motzkin var_count pre var)) post

    (*Verify if statement*)

    method verify_if (xpre : Types.extended_inv) (xinv : Types.extended_inv) (block1 : Types.block) (block2 : Types.block) (xpost : Types.extended_inv) : bool =
      (match s#last (fst block1) with
	 Some if_end_inv -> let if_beg_inv = List.hd (fst block1) in
			    (s#extended_verify_inv (s#extended_and_dnf xinv xpre) if_beg_inv)
			    && (s#extended_verify_inv if_end_inv xpost)
       | None            -> s#extended_verify_inv (s#extended_and_dnf xinv xpre) xpost)
      && (match s#last (fst block2) with
	    Some else_end_inv -> let else_beg_inv = List.hd (fst block2) in
				 (s#extended_verify_inv (s#extended_and_dnf xpre (s#extended_neg_dnf xinv)) else_beg_inv)
				 && (s#extended_verify_inv else_end_inv xpost)
	  | None              -> s#extended_verify_inv (s#extended_and_dnf xpre (s#extended_neg_dnf xinv)) xpost)
      && (s#verify_block block1)
      && (s#verify_block block2)

    (*Verify while statement*)

    method verify_while (xpre : Types.extended_inv) (xinv : Types.extended_inv) (block : Types.block) (xpost : Types.extended_inv) : bool =
      (match s#last (fst block) with
	 Some while_end_inv -> let while_beg_inv = List.hd (fst block) in
			       (s#extended_verify_inv (s#extended_and_dnf xinv xpre) while_beg_inv)
			       && (s#extended_verify_inv (s#extended_and_dnf xinv while_end_inv) while_beg_inv)
			       && (s#extended_verify_inv (s#extended_and_dnf while_end_inv (s#extended_neg_dnf xinv)) xpost)
       | None               -> true)
      && (s#extended_verify_inv (s#extended_and_dnf xpre (s#extended_neg_dnf xinv)) xpost)
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
