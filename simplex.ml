module Fraction =
  struct
    type frac = |Frac of int * int |Infty |Void

    (* greatest possible integer and greatest accepted integer *)

    let max_int = Int32.to_int Int32.max_int

    let max_acceptable_int = max_int / 100

    (* Print function *)

    let print_frac x = match x with
      |Frac(a, b) -> print_int a ; print_string " / " ; print_int b
      |Infty -> print_string "Infty"
      |Void -> print_string "Void"

    (* link with int *)

    let foi n = Frac (n, 1)

    let array_foi a =
      let n = Array.length a in
      let frac_a = Array.make n (foi 0) in
      for i = 0 to n - 1 do
        frac_a.(i) <- foi a.(i)
      done;
      frac_a

    let matrix_foi a =
      let n = Array.length a in
      let frac_a = Array.make n ([|foi 0|]) in
      for i = 0 to n - 1 do
        frac_a.(i) <- array_foi a.(i)
      done;
      frac_a

    (* Normalization functions *)

    let rec pgcd a b = match b with
      |0 -> abs a
      |b -> pgcd b (a mod b)

    let norm x = match x with
      |Frac(a, b) -> if a > max_acceptable_int || b > max_acceptable_int then failwith "Too big numbers" else let d = pgcd a b in if d = 0 then Frac(a, b) else if b > 0 then Frac(a / d, b / d) else Frac(-a / d, b / d)
      |_ -> Infty

    (* Algebraic operations *)

    let sum x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * d + c * b, b * d))
      |_-> Infty

    let sub x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * d - c * b, b * d))
      |_-> Infty

    let opp x = match x with
      |Frac(a, b) -> norm (Frac(-a, b))
      |_-> Infty

    let prod x y = match (x, y) with
      |Frac (a, b), Frac(c, d) -> norm (Frac(a * c, b * d))
      |_ -> Infty

    let inv x = match x with
      |Frac(0, _) -> Infty
      |Frac(a, b) -> norm (Frac(b, a))
      |_ -> Infty

    let div x y = prod x (inv y)

    (* Order relation *)

    let pos x = match x with
      |Frac(a, b) -> a * b >= 0
      | _ -> true

    let geq x y = match x, y with
      |Void, _                -> true
      |_, Infty               -> true
      |Infty, _               -> false
      |Frac(a, b), Frac(c, d) -> a * d >= b * c
      |_                      -> false

    let eq x y = match x, y with
      |Infty, Infty |Void, Void            -> true
      |Infty, _ |_, Infty |Void, _|_, Void -> false
      |Frac(a, b), Frac(c, d)              -> a * d = b * c

  end

open Fraction

module LinearOperations =
  struct

    let print_array a =
      let n = Array.length a in
      for i = 0 to n - 1 do
        print_frac a.(i); print_string " ; "
      done;
      print_string "\n"

    let print_matrix a = let n = Array.length a in
      for i = 0 to n - 1 do
        print_array a.(i);
      done

    let sum_line a m n i0 i1 lambda = (* a frac array of size m * n, adds lambda * line i1 to line i0  *)
      for j = 0 to n - 1 do
        a.(i0).(j) <- sum (a.(i0).(j)) (prod (a.(i1).(j)) lambda)
      done

    let prod_line a m n i0 lambda = (* a frac array of size m * n, multiplies line i0 by lambda *)
      for j = 0 to n - 1 do
        a.(i0).(j) <- prod lambda a.(i0).(j)
      done

    let is_base_column a n m j0 i0 = (* checks if column j0 has only zeros and one 1 from index i0*)
      let count = ref 0 in
      let nonzero_line = ref None in
      let i = ref i0 in
      while !i < n && (eq a.(!i).(j0) (foi 0) || eq a.(!i).(j0) (foi 1)) do
        if eq a.(!i).(j0) (foi 1) then (count := !count + 1 ; nonzero_line := Some (!i));
        i := !i + 1
      done;
    if !i = n && !count = 1 then !nonzero_line else None


    let pivot a n m i j =
      let x = a.(i).(j) in
      prod_line a n m i (inv x);
      for k = 0 to n - 1 do
        if not (k = i) then(
          let y = a.(k).(j) in
          sum_line a n m k i (opp y)
        )
      done

  end




open LinearOperations

(* Look whether the objective function can be bettered and find the most restrictive coefficient *)

let find_pivot a n m =
  (* Find a strictly positive coefficient in the objective function *)
  let j = ref 0 in
  while !j < (m - 1) && pos (opp a.(0).(!j)) do j := !j + 1 done;
  if !j = m - 1 then None else(
  let i = ref 1 in
  let lig = ref None in
  (* Look whether there is a strictly positive coefficient in the found column and find the most restrictive*)
  while !i < n do
    if not (pos (opp a.(!i).(!j))) then (
      match !lig with
      |None -> lig := Some !i
      |Some i0 -> let c = pos (sum (prod (inv a.(i0).(!j)) a.(i0).(m - 1)) (opp (prod (inv a.(!i).(!j)) a.(!i).(m - 1)))) in if c then lig := Some !i;
    );
    i := !i + 1;
  done;
  Some(Some !j, !lig))

(* Build a canonical simplex array given an ordinary one *)

let to_canonical ab k l =
  let simplex_array = Array.make (k + 1) [||] in
  for i = 0 to k do
    let idlig = Array.make k (foi 0) in
    if i > 0 then idlig.(i - 1) <- (foi 1);
    simplex_array.(i) <- Array.append idlig ab.(i)
  done;
  simplex_array

(* build a canonical simplex array given a.(0) the objective function, a.(i) the constraints and b the constant values of the affine forms with b coefficients >= 0 *)

let init_simplex a b k l =
  let ab = Array.make (k + 1) [||] in
  for i = 0 to k do
    ab.(i) <- Array.append a.(i) [|b.(i)|]
  done;
  to_canonical ab k l

(* Solve the simplex given a canonical array *)

let simplex_basis simplex_array k l =
  let rec simplex_rec simplex_array k l =
    let piv = find_pivot simplex_array (k + 1) (k + l + 2) in match piv with
      |None -> simplex_array.(0).(k + l + 1)
      |Some (_, None) -> Infty
      |Some (Some j, Some i) ->
        pivot simplex_array (k + 1) (k + l + 2) i j ;
        simplex_rec simplex_array k l
      |_ -> Infty
  in simplex_rec simplex_array k l

(* Solve the simplex with a the linear parts of the affine forms, b their constant parts, k the number of base variables, (l + 1) the number of non-base variables *)

let simplex a b k l =
  (* Build the canonical simplex array *)
  let simplex_array = init_simplex a b k l in
  (* Check whether there is a negative constant *)
  let count = ref 0 in
  for i = 1 to k do
    if not (pos b.(i)) then (
      count := !count + 1;
      for j = 0 to k + l + 1 do
        simplex_array.(i).(j) <- opp simplex_array.(i).(j)
      done
    )
  done;
  (* If there is no negative constant, then apply the simplex *)
  if !count = 0 then simplex_basis simplex_array k l
  (* Add auxiliary variables to each line and minimize their sum to have positive constants *)
  else(

    let original_objective = Array.copy simplex_array.(0) in
    simplex_array.(0) <- Array.make (k + l + 2) (foi 0);
    for i = 1 to k do
      sum_line simplex_array (k + 1) (k + l + 2) 0 i (foi (1))
    done;
    (* Minimize the sum of the auxiliary variables and check whether it can be zero *)
    let feasibility_simplex_array = to_canonical simplex_array k (k + l) in
    let feasible = simplex_basis feasibility_simplex_array k (k + l) in
    if not (eq feasible (foi 0)) then Void
    else(
      (* Make sure no auxiliary variable is a base variable *)
      for j = 0 to (k - 1) do
        match is_base_column feasibility_simplex_array (k + 1) (k + 2 * l + 2) j 0 with
          |None -> ()
          |Some i0 ->
            let flag = ref true in
            let jj = ref k in
            while !flag && !jj < (k + 2 * l + 2) do
              if (not (eq feasibility_simplex_array.(i0).(!jj) (foi 0))) && (is_base_column feasibility_simplex_array (k + 1) (k + 2 * l + 2) !jj 0) = None then (
                pivot feasibility_simplex_array (k + 1) (k + 2 * l + 2) i0 !jj;
                flag := false
              );
              jj := !jj + 1
            done
      done;
      (* Get rid of the auxiliary variables *)
      simplex_array.(0) <- original_objective;
      for i = 1 to k do
        simplex_array.(i) <- Array.sub feasibility_simplex_array.(i) k (k + l + 2)
      done;
      for j = 0 to (k + l) do
        match is_base_column simplex_array (k + 1) (k + l + 2) j 1 with
          |None -> ()
          |Some i0 ->
            pivot simplex_array (k + 1) (k + l + 2) i0 j
      done;
      (* Back to the positive constants case *)
      simplex_basis simplex_array k l
    )
  )
