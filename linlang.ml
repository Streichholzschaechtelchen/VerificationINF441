open Simplex
open FourrierMotzkin

(*Conversion from parsing types to (abstract) analysis types*)
       
let abstract_expr var_count var_codes pexpr =
  let s_expr = Array.make (var_count + 1) (Fraction.foi 0) in
  List.iter (fun x -> match x with
			None,   i -> s_expr.(var_count) <- Fraction.sum s_expr.(var_count) (Fraction.foi i)
		      | Some v, i -> begin
				     if Hashtbl.mem var_codes v
				     then s_expr.(Hashtbl.find var_codes v)
					  <- Fraction.sum s_expr.(Hashtbl.find var_codes v) (Fraction.foi i)
				     else failwith ("Variable " ^ v ^ " not bound")
				   end
	   )
	   (snd pexpr);
  (fst pexpr), s_expr

let abstract_inv var_count var_codes pinv =
  List.map (abstract_expr var_count var_codes) pinv
		
let rec abstract_instr var_count var_codes = function
    Types.PAssignment (pvar, pexpr) -> begin
				      if Hashtbl.mem var_codes pvar
				      then Types.Assignment (Hashtbl.find var_codes pvar,
							      abstract_expr var_count var_codes pexpr)
				      else failwith ("Variable " ^ pvar ^ " not bound")
				    end
  | Types.PIf (inv, block1, block2) -> Types.If (abstract_inv var_count var_codes inv,
					   abstract_block var_count var_codes block1,
					   abstract_block var_count var_codes block2)
  | Types.PWhile (inv, block)       -> Types.While (abstract_inv var_count var_codes inv,
					      abstract_block var_count var_codes block)
and abstract_block var_count var_codes pblock =
  let pinvs, pinstrs = pblock in
  List.map (abstract_inv var_count var_codes) pinvs,
  List.map (abstract_instr var_count var_codes) pinstrs

let abstract_prog pprog =
  (*create the hashtable encoding variable indices*)
  let var_codes = Hashtbl.create 10 in
  let pvars, pblock = pprog in
  List.iteri (fun i v -> if Hashtbl.mem var_codes v
			then failwith ("Duplicate variable " ^ v)
			else Hashtbl.add var_codes v i)
	     pvars;
  let var_count = List.length pvars in
  (*convert pprog to prog*)
  var_count, abstract_block var_count var_codes pblock

(*Verify implication inv0 => expr using the simplex algorithm*)

let opp_expr expr =
  fst expr, Array.map Fraction.opp (snd expr)

let neg_ineq var_count ineq =
  fst ineq, Array.mapi(fun i x -> if i = var_count
				  then (Fraction.sum (Fraction.opp x)
						     (Fraction.foi (-1)))
				  else (Fraction.opp x))
		      (snd ineq)

let vars_from_z_to_n var_count s_expr =
  let vars_only = Array.sub s_expr 0 var_count in
  Array.append vars_only (Array.map Fraction.opp vars_only)
			    
let verify_expr var_count inv0 expr =
  let f_expr, s_expr = expr in
  let k = List.length inv0 in
  let l = 2 * var_count - 1 in
  let b = Array.of_list (s_expr.(var_count)::(List.map (fun x -> (snd x).(var_count)) inv0)) in
  let a = Array.of_list ((vars_from_z_to_n var_count s_expr)::(List.map (vars_from_z_to_n var_count) (List.map snd inv0))) in
  print_string "Verifying expression line ";
  print_int f_expr;
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
  else begin print_string "Failed verifying expression line ";
	     print_int f_expr;
	     print_string ", minimum is ";
	     Fraction.print_frac simplex_min;
	     print_newline ()
       end;
  result

let verify_inv var_count inv0 inv =
  List.fold_left (&&) true (List.map (verify_expr var_count inv0) inv)

(*Verify assignment : auxiliary functions*)

let update_expr var_count var expr0 expr =
  let f_expr, s_expr = expr in
  let _, s_expr0 = expr0 in
  let coeff = Fraction.div s_expr.(var) s_expr0.(var) in
  f_expr, Array.mapi (fun j x -> match j with
				   i when i = var -> coeff
				 | i              -> Fraction.sum x (Fraction.opp (Fraction.prod coeff s_expr0.(i)))
		     ) s_expr

let update_inv var_count var expr0 inv =
  List.map (update_expr var_count var expr0) inv

let rec last = function
    []   -> None
  | [h]  -> Some h
  | h::t -> last t

(*Verify assignment*)

let verify_assignment var_count pre var expr post =
  let f_expr, s_expr = expr in
  if not (Fraction.eq s_expr.(var) (Fraction.foi 0))
  then (*cas d'une affectation inversible*)
    verify_inv var_count (update_inv var_count var expr pre) post
  else (*cas d'une affectation non inversible*)
    let oned_expr = f_expr, Array.mapi (fun i x -> if i = var then (Fraction.foi (-1)) else x) s_expr in
    verify_inv var_count ((oned_expr)::(opp_expr oned_expr)::(fourrier_motzkin var_count pre var)) post
	       
(*Verify if statement*)

let rec verify_and_not var_count pre inv post =
  List.for_all (fun x -> verify_inv var_count ((neg_ineq var_count x)::pre) post) inv

let rec verify_if var_count pre inv block1 block2 post =
  (match last (fst block1) with
     Some if_end_inv -> let if_beg_inv = List.hd (fst block1) in
			(verify_inv var_count (inv@pre) if_beg_inv)
			&& (verify_inv var_count if_end_inv post)
   | None            -> verify_inv var_count (inv@pre) post)
  && (match last (fst block2) with
	Some else_end_inv -> let else_beg_inv = List.hd (fst block2) in
			     (verify_and_not var_count pre inv else_beg_inv)
			     && (verify_inv var_count else_end_inv post)
      | None              -> verify_and_not var_count pre inv post)
  && (verify_block var_count block1)
  && (verify_block var_count block2)

(*Verify while statement*)
       
and verify_while var_count pre inv block post =
  (match last (fst block) with
     Some while_end_inv -> let while_beg_inv = List.hd (fst block) in
			  (verify_inv var_count (inv@pre) while_beg_inv)
			  && (verify_inv var_count (inv@while_end_inv) while_beg_inv)
			  && (verify_and_not var_count while_end_inv inv post)
   | None               -> true)
  && (verify_and_not var_count pre inv post)
  && (verify_block var_count block)

(*Verify whole block*)
							   
and verify_block var_count block = match block with
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
  Printer.print_prog pprog; flush stdout;
  let var_count, proc = abstract_prog pprog in
  if (verify_block var_count proc)
  then print_string "Verified!\n"
  else print_string "Could not be verified.\n"; 
  ()
