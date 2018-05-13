open Simplex

(*Printing functions*)

let rec loop f = function
    0            -> ()
  | i when i < 0 -> failwith "loop counter should not be negative"
  | i            -> begin f (); loop f (i - 1) end

let rec print_chars c =
  loop (fun _ -> print_char c)

let rec print_tabs = print_chars '\t'

let rec erase i =
  print_chars '\b' i;
  print_chars ' ' i;
  print_chars '\b' i

let print_expr expr =
  let _ = List.map (fun x -> match x with
			       None, value       -> begin
						   print_int value;
						   print_string " + "
						 end
			     | (Some var), value -> begin
						    print_int value;
						    print_string " * ";
						    print_string var;
						    print_string " + "
						  end
		   ) expr in
  erase 3; ()

let print_inv inv =
  let _ = List.map (fun x -> print_expr x; print_string " >= 0 and ")
		   inv in
  erase 5; ()

let print_prog prog =
  print_string "======\nVariables:\n";
  let _ = List.map (fun x -> print_string x; print_string " ") (fst prog) in
  print_string "\n======\nProgram:\n";
  let rec aux i = function
      []
      -> ()
    | (Types.PAssignment (var, expr))::t  
      -> begin
	 print_tabs i;
	 print_string var;
	 print_string " <- ";
	 print_expr expr;
	 print_newline ();
	 aux i t
       end
    | (Types.PIf (inv, block1, block2))::t
      -> begin
	 print_tabs i;
	 print_string "If ";
	 print_inv inv;
	 print_newline ();
	 aux (i + 1) (snd block1);
	 print_tabs i;
	 print_string "Else\n";
	 aux (i + 1) (snd block2);
	 aux i t
       end
    | (Types.PWhile (inv, block))::t
      -> begin
	 print_tabs i;
	 print_string "While ";
	 print_inv inv;
	 print_newline ();
	 aux (i + 1) (snd block);
	 aux i t
       end
  in aux 0 (snd (snd prog));
     print_string "======\n";
     ()

(*Conversion from parsing types to (abstract) analysis types*)
       
let abstract_expr var_count var_codes pexpr =
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

let verify_expr var_count inv0 expr =
  let k = List.length inv0 in
  let l = var_count - 1 in
  let b = Array.of_list (expr.(var_count)::(List.map (fun x -> x.(var_count)) inv0)) in
  let a = Array.of_list ((Array.sub expr 0 var_count)::(List.map (fun x -> Array.sub x 0 var_count) inv0)) in
  print_string "Sending k:\n"; print_int k; print_newline ();
  print_string "Sending l:\n"; print_int l; print_newline ();
  print_string "Sending a:\n"; print_matrix a;
  print_string "Sending b:\n"; print_array b;
  print_newline ();
  let result = Fraction.geq (simplex a b k l) (Fraction.foi 0) in
  if result
  then print_string "Expression verified!\n"
  else print_string "Expression not verified.\n";
  result

let verify_inv var_count inv0 inv =
  List.fold_left (&&) true (List.map (verify_expr var_count inv0) inv)

(*Workaround : no Array.map2 for OCaml < 4.03*)

let array_map2 f a1 a2 =
  Array.of_list (List.map2 f (Array.to_list a1) (Array.to_list a2))

(*Fourrier_Motzkin algorithm*)

let fourrier_motzkin var_count inv var =
  let normalize expr positive =
    let coeff = if not positive
		then Fraction.inv expr.(var)
		else Fraction.opp (Fraction.inv expr.(var))				  
    in
    Array.mapi (fun i x -> if i <> var_count
			      then Fraction.prod x coeff
			      else Fraction.opp (Fraction.prod x coeff)
		  )		  expr
  in 
  let substract expr1 expr2 =
    array_map2 (Fraction.sub) expr1 expr2
  in
  let rec split = function
      []
      -> [], []
    | expr::t when Fraction.geq expr.(var) (Fraction.foi 0)
      -> let a, b = split t in (normalize expr true)::a, b
    | expr::t
      -> let a, b = split t in a, (normalize expr false)::b
  in
  let a, b = split inv in
  let rec aux1 acc h = function
      []   -> acc
    | k::t -> aux1 ((substract k h)::acc) h t
  in
  let rec aux0 acc = function
      []   -> acc
    | h::t -> aux0 (aux1 acc h b) t
  in
  aux0 [] a

(*Verify assignment : auxiliary functions*)

let update_expr var_count var expr0 expr =
  let coeff = Fraction.div expr.(var) expr0.(var) in
  Array.mapi (fun j x -> match j with
			   i when i = var -> coeff
			 | i              -> Fraction.sum x (Fraction.opp (Fraction.prod coeff expr0.(i)))
	     ) expr

let update_inv var_count var expr0 inv =
  List.map (update_expr var_count var expr0) inv

let rec last = function
    []   -> None
  | [h]  -> Some h
  | h::t -> last t

let rec invert_inv inv =
  List.map (Array.map Fraction.opp) inv

(*Verify assignment*)

let verify_assignment var_count pre var expr post =
  if not (Fraction.eq expr.(var) (Fraction.foi 0))
  then (*cas d'une affectation inversible*)
    verify_inv var_count (update_inv var_count var expr pre) post
  else (*cas d'une affectation non inversible*)
    verify_inv var_count ((Array.mapi (fun i x -> if i = var then (Fraction.foi (-1)) else x) expr)
                          ::(Array.mapi (fun i x -> if i = var then (Fraction.foi 1) else x) expr)
	                  ::(fourrier_motzkin var_count pre var)) post
	       
(*Verify if statement*)

let rec verify_if var_count pre inv block1 block2 post =
  (match last (fst block1) with
     Some if_end_inv -> let if_beg_inv = List.hd (fst block1) in
			(verify_inv var_count (inv@pre) if_beg_inv)
			&& (verify_inv var_count if_end_inv post)
   | None            -> verify_inv var_count (inv@pre) post)
  && (match last (fst block2) with
	Some else_end_inv -> let else_beg_inv = List.hd (fst block2) in
			     (verify_inv var_count ((invert_inv inv)@pre) else_beg_inv)
			     && (verify_inv var_count else_end_inv post)
      | None              -> verify_inv var_count ((invert_inv inv)@pre) post)
  && (verify_block var_count block1)
  && (verify_block var_count block2)

(*Verify while statement*)
       
and verify_while var_count pre inv block post =
  (match last (fst block) with
     Some while_end_inv -> let while_beg_inv = List.hd (fst block) in
			  (verify_inv var_count (inv@pre) while_beg_inv)
			  && (verify_inv var_count (inv@while_end_inv) while_beg_inv)
			  && (verify_inv var_count ((invert_inv inv)@while_end_inv) post)
   | None               -> true)
  && (verify_inv var_count ((invert_inv inv)@pre) post)
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
  print_prog pprog; flush stdout;
  let var_count, proc = abstract_prog pprog in
  if (verify_block var_count proc)
  then print_string "Verified!"
  else print_string "Could not be verified."; 
  ()
