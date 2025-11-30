
type literal = int * bool        (* (var, is_negated) *)
type clause = literal list
type formula = clause list

type state = {
  mutable value      : bool option array;      
  mutable antecedent : clause option array;   
  mutable dl         : int array;             
}

(** Create initial state for num_vars variables *)
let make_state (num_vars : int) : state =
  {
    value      = Array.make (num_vars + 1) None;
    antecedent = Array.make (num_vars + 1) None;
    dl         = Array.make (num_vars + 1) 0;
  }

(** Convert DIMACS integers to internal (var, negated) representation *)
let convert_clause (lit_list : int list) : clause =
  List.map (fun lit ->
    let var = abs lit in
    let neg = lit < 0 in
    (var, neg)
  ) lit_list

(** Get all variables from formula *)
let get_variables (formula : formula) : int list =
  let vars = ref [] in
  List.iter (fun clause ->
    List.iter (fun (var, _) ->
      if not (List.mem var !vars) then
        vars := var :: !vars
    ) clause
  ) formula;
  List.sort compare !vars

(** Evaluate a literal under current state
    Returns Some(bool) if assigned, None if unassigned *)
let eval_literal (var : int) (neg : bool) (state : state) : bool option =
  match state.value.(var) with
  | Some v -> Some (if neg then not v else v)
  | None -> None

(** Determine status of a clause: 'S' (satisfied), 'U' (unit), 'C' (conflict), 'R' (unresolved) *)
let clause_status (clause : clause) (state : state) : char =
  let results = List.map (fun (var, neg) ->
    eval_literal var neg state
  ) clause in
  
  if List.mem (Some true) results then
    'S'  (* satisfied *)
  else if List.for_all (fun r -> r = Some false) results then
    'C'  (* conflict *)
  else if List.filter (fun r -> r = None) results |> List.length = 1 then
    'U'  (* unit *)
  else
    'R'  (* unresolved *)

(** Find unassigned literal in unit clause *)
let find_unit_literal (clause : clause) (state : state) : literal option =
  List.find_opt (fun (var, _) ->
    state.value.(var) = None
  ) clause

(** Unit propagation: repeatedly assign unit clause literals *)
let unit_propagation (formula : formula) (state : state) (current_dl : int)
    : clause option =
  let rec loop () =
    let found_unit = ref false in
    let conflict = ref None in
    
    List.iter (fun clause ->
      match clause_status clause state with
      | 'S' | 'R' -> ()
      | 'C' -> conflict := Some clause
      | 'U' ->
          (match find_unit_literal clause state with
           | Some (var, neg) ->
               let value = not neg in
               state.value.(var) <- Some value;
               state.antecedent.(var) <- Some clause;
               state.dl.(var) <- current_dl;
               found_unit := true
           | None -> ())
      | _ -> ()
    ) formula;
    
    match !conflict with
    | Some c -> c
    | None -> if !found_unit then loop () else (
        (* No conflict, check if all satisfied *)
        List.find_map (fun clause ->
          match clause_status clause state with
          | 'C' -> Some clause
          | _ -> None
        ) formula
        |> (function Some c -> c | None -> raise Not_found)
      )
  in
  try
    Some (loop ())
  with Not_found -> None

(** Pick first unassigned variable with value True *)
let pick_branching_variable (variables : int list) (state : state)
    : (int * bool) option =
  let unassigned = List.find_opt (fun var ->
    state.value.(var) = None
  ) variables in
  match unassigned with
  | None -> None
  | Some var -> Some (var, true)

(** Backtrack: remove assignments with decision level > b *)
let backtrack (state : state) (b : int) : unit =
  for v = 1 to Array.length state.value - 1 do
    if state.dl.(v) > b then (
      state.value.(v) <- None;
      state.antecedent.(v) <- None;
      state.dl.(v) <- 0
    )
  done

(** Resolve two clauses on variable x
    Removes x from both clauses and combines remaining literals *)
let resolve (clause_a : clause) (clause_b : clause) (x : int) : clause =
  let filtered_a = List.filter (fun (var, _) -> var <> x) clause_a in
  let filtered_b = List.filter (fun (var, _) -> var <> x) clause_b in
  let combined = filtered_a @ filtered_b in
  
  (* Remove duplicates *)
  let seen = Hashtbl.create (List.length combined) in
  List.filter (fun lit ->
    if Hashtbl.mem seen lit then false
    else (Hashtbl.add seen lit (); true)
  ) combined

(** Conflict analysis using First UIP strategy
    Returns (backtrack_level, learned_clause) *)
let conflict_analysis (conflict_clause : clause) (state : state) (current_dl : int)
    : int * clause =
  if current_dl = 0 then
    (-1, conflict_clause)
  else
    let current = ref conflict_clause in
    
    let rec analyze () =
      (* Count literals at current decision level *)
      let current_level_lits = List.filter (fun (var, _) ->
        state.dl.(var) = current_dl
      ) !current in
      
      if List.length current_level_lits <= 1 then
        !current
      else
        (* Find an implied literal (one with antecedent) *)
        let implied = List.find_opt (fun (var, _) ->
          state.antecedent.(var) <> None
        ) current_level_lits in
        
        match implied with
        | None -> !current
        | Some (var, _) ->
            (match state.antecedent.(var) with
             | Some antecedent ->
                 current := resolve !current antecedent var;
                 analyze ()
             | None -> !current)
    in
    
    let learned = analyze () in
    
    (* Compute backtrack level: second-highest decision level *)
    let decision_levels = ref [] in
    List.iter (fun (var, _) ->
      if state.dl.(var) > 0 then
        decision_levels := state.dl.(var) :: !decision_levels
    ) learned;
    
    let decision_levels = List.sort_uniq compare !decision_levels in
    let backtrack_level =
      match List.rev decision_levels with
      | [] -> 0
      | [_] -> 0
      | _ :: b :: _ -> b
      | _ -> 0
    in
    
    (backtrack_level, learned)

(** Main CDCL solver *)
let solve_sat (num_vars : int) (raw_clauses : int list list) : bool option array option =
  (* Convert to internal format *)
  let formula = List.map convert_clause raw_clauses in
  let variables = get_variables formula in
  
  (* Initialize state *)
  let state = make_state num_vars in
  let current_dl = ref 0 in
  let formula_ref = ref formula in
  
  (* Initial unit propagation *)
  (match unit_propagation !formula_ref state !current_dl with
   | Some _ -> None  (* UNSAT from start *)
   | None -> ());
  
  (* Main CDCL loop *)
  let rec solve () =
    (* Check if all variables assigned *)
    let assigned_count = ref 0 in
    for v = 1 to num_vars do
      if state.value.(v) <> None then incr assigned_count
    done;
    
    if !assigned_count = num_vars then
      (* SAT: all variables assigned *)
      Some state.value
    else
      match pick_branching_variable variables state with
      | None -> Some state.value
      | Some (var, value) ->
          incr current_dl;
          state.value.(var) <- Some value;
          state.antecedent.(var) <- None;
          state.dl.(var) <- !current_dl;
          
          let rec propagate_and_analyze () =
            match unit_propagation !formula_ref state !current_dl with
            | None -> solve ()
            | Some conflict ->
                let (backtrack_level, learned) =
                  conflict_analysis conflict state !current_dl in
                
                if backtrack_level < 0 then
                  None  (* UNSAT *)
                else (
                  formula_ref := !formula_ref @ [learned];
                  backtrack state backtrack_level;
                  current_dl := backtrack_level;
                  propagate_and_analyze ()
                )
          in
          
          propagate_and_analyze ()
  in
  
  solve ()
