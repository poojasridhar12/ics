(* main.ml - Main entry point for CDCL SAT solver *)

open Printf

let main () =
  if Array.length Sys.argv <> 3 then (
    printf "Usage: ocaml main.ml <input_file> <output_file>\n";
    exit 1
  );
  
  let input_file = Sys.argv.(1) in
  let output_file = Sys.argv.(2) in
  
  try
    let (num_vars, clauses) = Parser.parse_dimacs input_file in
    
    printf "Solving SAT instance with %d variables and %d clauses...\n" 
      num_vars (List.length clauses);
    
    let start_time = Unix.gettimeofday () in
    
    let assignment = Sat_solver.solve_sat num_vars clauses in
    
    let end_time = Unix.gettimeofday () in
    printf "Solved in %.4f seconds\n" (end_time -. start_time);
    
    Parser.write_solution output_file assignment;
    
    (match assignment with
     | Some _ -> printf "SAT - Solution found!\n"
     | None -> printf "UNSAT - No solution exists\n");
    
    exit 0
    
  with
  | Sys_error msg -> 
      printf "Error: %s\n" msg;
      exit 1
  | e ->
      printf "Error: %s\n" (Printexc.to_string e);
      exit 1

let () = main ()
