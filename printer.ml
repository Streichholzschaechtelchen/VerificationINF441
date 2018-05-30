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

let print_pexpr pexpr =
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
		   ) pexpr in
  erase 3; ()

let rec print_pinv = function
    Types.Naught (_)     -> ()
  | Types.PUnsat (_)      -> print_string "unsat"
  | Types.Expr (_, ineq) -> begin
			    print_pexpr ineq;
			    print_string " >= 0"
			  end
  | Types.Not (_, inv)   -> begin
			    print_string "NOT (";
			    print_pinv inv;
			    print_string ")"
			  end
  | Types.And (_, invl)  -> begin
			    print_string "(";
			    List.iter (fun x -> print_pinv x;
						print_string ") AND (")
				      invl;
			    erase 6
			  end
  | Types.Or (_, invl)   -> begin
			    print_string "(";
			    List.iter (fun x -> print_pinv x;
						print_string ") OR (")
				      invl;
			    erase 6
			  end

let print_pprog pprog =
  print_string "======\nVariables:\n";
  let _ = List.map (fun x -> print_string x; print_string " ") (fst pprog) in
  print_string "\n======\nProgram:\n";
  let rec aux i = function
      [] , []
      -> begin
	print_tabs i;
	print_string "{  }";
	print_newline ()
      end
     | [inv0], []
      -> begin
	print_tabs i;
	print_string "{ ";
	print_pinv inv0;
	print_string " }";
	print_newline ()
      end
    | inv0::t0, (Types.PAssignment (var, expr))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_pinv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string var;
	 print_string " <- ";
	 print_pexpr expr;
	 print_newline ();
	 aux i (t0, t)
       end
    | inv0::t0, (Types.PIf (inv, block1, block2))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_pinv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "If ";
	 print_pinv inv;
	 print_newline ();
	 aux (i + 1) block1;
	 print_tabs i;
	 print_string "Else\n";
	 aux (i + 1) block2;
	 aux i (t0, t)
       end
    | inv0::t0, (Types.PWhile (inv, block))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_pinv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "While ";
	 print_pinv inv;
	 print_newline ();
	 aux (i + 1) block;
	 aux i (t0, t)
       end
    | _, _
      -> failwith "this case should never occur"
  in aux 0 (snd pprog);
     print_string "======\n";
     ()

let print_expr var_count expr =
  Array.iteri (fun i x -> begin if (i = var_count) then begin
				  		     Simplex.Fraction.print_frac x;
						     print_string " + "
						   end
				else begin
	  			    print_string "x_";
				    print_int i;
				    print_string " * ";
				    Simplex.Fraction.print_frac x;
				    print_string " + "
				  end
			  end

	      ) expr;
    erase 3; ()

let rec print_inv var_count inv =
  print_string "#";
  print_int (fst inv);
  print_string ": ";
  List.iter (fun conj -> begin List.iter (fun expr -> print_expr var_count expr;
						      print_string " >= 0 AND ")
					 conj;
			       erase 5;
			       print_string " OR "
			 end)
	    (snd inv);
  erase 4

let print_extended_inv var_count xinv =
  match xinv with
  |Types.Inv inv -> print_inv var_count inv
  |Types.Unsat (x) ->
    print_string "#";
    print_int x;
    print_string ": unsat"

let print_prog (prog : Types.prog) : unit =
  let var_count = fst prog in
  print_string "======\nVariables:\n";
  print_int var_count;
  print_string "\n======\nProgram:\n";
  let rec aux (i : int) : Types.block -> unit = function
      [inv0], []
      -> begin
	print_tabs i;
	print_string "{ ";
	print_extended_inv var_count inv0;
	print_string " }";
	print_newline ()
      end
    | inv0::t0, (Types.Assignment (var, expr))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_extended_inv var_count inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "x_";
	 print_int var;
	 print_string " <- ";
	 print_expr var_count expr;
	 print_newline ();
	 aux i (t0, t)
       end
    | inv0::t0, (Types.If (inv, block1, block2))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_extended_inv var_count inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "If ";
	 print_extended_inv var_count inv;
	 print_newline ();
	 aux (i + 1) block1;
	 print_tabs i;
	 print_string "Else\n";
	 aux (i + 1) block2;
	 aux i (t0, t)
       end
    | inv0::t0, (Types.While (inv, block))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_extended_inv var_count inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "While ";
	 print_extended_inv var_count inv;
	 print_newline ();
	 aux (i + 1) block;
	 aux i (t0, t)
       end
    | _, _
      -> failwith "this case should never occur"
  in aux 0 (snd prog);
     print_string "======\n";
     ()
