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
		   ) (snd expr) in
  erase 3; ()

let print_inv inv =
  let _ = List.map (fun x -> print_expr x; print_string " >= 0 and ") inv
  in if inv <> [] then erase 5; ()

let print_prog prog =
  print_string "======\nVariables:\n";
  let _ = List.map (fun x -> print_string x; print_string " ") (fst prog) in
  print_string "\n======\nProgram:\n";
  let rec aux i = function
      [inv0], []
      -> begin
	print_tabs i;
	print_string "{ ";
	print_inv inv0;
	print_string " }";
	print_newline ()
      end
    | inv0::t0, (Types.PAssignment (var, expr))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_inv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string var;
	 print_string " <- ";
	 print_expr expr;
	 print_newline ();
	 aux i (t0, t)
       end
    | inv0::t0, (Types.PIf (inv, block1, block2))::t
      -> begin
	 print_tabs i;
	 print_string "{ ";
	 print_inv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "If ";
	 print_inv inv;
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
	 print_inv inv0;
	 print_string " }";
	 print_newline ();
	 print_tabs i;
	 print_string "While ";
	 print_inv inv;
	 print_newline ();
	 aux (i + 1) block;
	 aux i (t0, t)
       end
    | _, _
      -> failwith "this case should never occur"
  in aux 0 (snd prog);
     print_string "======\n";
     ()
