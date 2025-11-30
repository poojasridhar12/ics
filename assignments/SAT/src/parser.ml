(** Parse a DIMACS CNF file and returns: (num_vars, clauses) where clauses is a list of int lists *)
let parse_dimacs (filename : string) : int * int list list =
  let ic = open_in filename in
  let lines = ref [] in
  
  (* Read all lines *)
  (try
    while true do
      lines := input_line ic :: !lines
    done
  with End_of_file -> close_in ic);
  
  let lines = List.rev !lines in
  let num_vars = ref 0 in
  let clauses = ref [] in
  
  (* Process each line *)
  List.iter (fun line ->
    let line = String.trim line in
    
    (* Skip empty lines and comments *)
    if String.length line = 0 then
      ()
    else if String.length line > 0 && line.[0] = 'c' then
      ()
    (* Parse problem line: p cnf <num_vars> <num_clauses> *)
    else if String.length line > 0 && line.[0] = 'p' then (
      let parts = String.split_on_char ' ' line in
      let parts = List.filter (fun s -> String.length s > 0) parts in
      match parts with
      | "p" :: "cnf" :: nv_str :: _ ->
          (try num_vars := int_of_string nv_str with _ -> ())
      | _ -> ()
    )
    (* Parse clause line: <lit1> <lit2> ... <litN> 0 *)
    else (
      let parts = String.split_on_char ' ' line in
      let parts = List.filter (fun s -> String.length s > 0) parts in
      let clause = ref [] in
      
      List.iter (fun part ->
        try
          let lit = int_of_string part in
          if lit <> 0 then
            clause := lit :: !clause
        with _ -> ()
      ) parts;
      
      if !clause <> [] then
        clauses := (List.rev !clause) :: !clauses
    )
  ) lines;
  
  (!num_vars, List.rev !clauses)


(** Write solution to output file in DIMACS format
    assign: None for UNSAT, Some (value_array) for SAT
    where value_array.(v) = Some true/false if assigned, None if unassigned *)
let write_solution (filename : string)
    (assignment : bool option array option) : unit =
  let oc = open_out filename in
  
  (match assignment with
   | None ->
       (* UNSAT case *)
       output_string oc "UNSAT\n"
   | Some value_array ->
       (* SAT case *)
       output_string oc "SAT\n";
       
       (* Collect assigned variables *)
       let assigned = ref [] in
       Array.iteri (fun v opt_val ->
         if v > 0 then  (* Skip index 0 *)
           match opt_val with
           | Some b ->
               let lit = if b then v else -v in
               assigned := (v, lit) :: !assigned
           | None -> ()
       ) value_array;
       
       (* Sort by variable number *)
       let assigned = List.sort (fun (v1, _) (v2, _) -> compare v1 v2) !assigned in
       
       (* Write literals *)
       List.iter (fun (_, lit) ->
         Printf.fprintf oc "%d " lit
       ) assigned;
       
       output_string oc "0\n"
  );
  
  close_out oc
