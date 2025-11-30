

(** Type definitions *)
type literal = int * bool
type clause = literal list

(** Watch structure: each clause tracks 2 watched literal indices *)
type watched_clause = {
  lits: clause;
  mutable watch1: int;  (* index into lits *)
  mutable watch2: int;  (* index into lits *)
}

type state = {
  mutable value      : bool option array;
  mutable antecedent : int option array;  (* clause index instead of clause *)
  mutable dl         : int array;
  mutable vsids_activity : float array;   (* VSIDS scores *)
  mutable phase_saved : bool array;       (* saved phases *)
}

type solver_state = {
  clauses: watched_clause array;
  watches: (int, int list ref) Hashtbl.t;  (* literal -> clause indices *)
  state: state;
  mutable num_conflicts: int;
  mutable vsids_inc: float;
  mutable vsids_decay: float;
}

(** Constants *)
let vsids_decay_factor = 0.95
let vsids_initial_inc = 1.0
let restart_base = 100
let restart_inc = 1.5

(** Convert DIMACS to internal format *)
let convert_clause (lit_list : int list) : clause =
  List.map (fun lit ->
    let var = abs lit in
    let neg = lit < 0 in
    (var, neg)
  ) lit_list

(** Create initial state *)
let make_state (num_vars : int) : state =
  {
    value      = Array.make (num_vars + 1) None;
    antecedent = Array.make (num_vars + 1) None;
    dl         = Array.make (num_vars + 1) 0;
    vsids_activity = Array.make (num_vars + 1) 0.0;
    phase_saved = Array.make (num_vars + 1) true;
  }

(** Initialize watched literals for a clause *)
let init_watched_clause (lits : clause) : watched_clause =
  let len = List.length lits in
  {
    lits = lits;
    watch1 = 0;
    watch2 = if len > 1 then 1 else 0;
  }

(** Convert literal to watch key *)
let lit_to_key (var : int) (neg : bool) : int =
  if neg then -var else var

(** Evaluate literal *)
let eval_literal (var : int) (neg : bool) (state : state) : bool option =
  match state.value.(var) with
  | Some v -> Some (if neg then not v else v)
  | None -> None

(** Get literal at index in watched clause *)
let get_lit (wc : watched_clause) (idx : int) : literal =
  List.nth wc.lits idx

(** Update VSIDS activity for a variable *)
let bump_activity (solver : solver_state) (var : int) : unit =
  solver.state.vsids_activity.(var) <- 
    solver.state.vsids_activity.(var) +. solver.vsids_inc;
  
  (* Rescale if needed *)
  if solver.state.vsids_activity.(var) > 1e100 then (
    for i = 1 to Array.length solver.state.vsids_activity - 1 do
      solver.state.vsids_activity.(i) <- 
        solver.state.vsids_activity.(i) *. 1e-100
    done;
    solver.vsids_inc <- solver.vsids_inc *. 1e-100
  )

(** Decay VSIDS scores *)
let decay_activities (solver : solver_state) : unit =
  solver.vsids_inc <- solver.vsids_inc /. solver.vsids_decay

(** Two-watched literal unit propagation *)
let unit_propagation (solver : solver_state) (current_dl : int) 
    : int option =
  let queue = Queue.create () in
  let state = solver.state in
  
  (* Initialize queue with all assigned literals *)
  Array.iteri (fun var opt_val ->
    if var > 0 then
      match opt_val with
      | Some v -> 
          let key = lit_to_key var (not v) in
          Queue.add key queue
      | None -> ()
  ) state.value;
  
  let conflict = ref None in
  
  while not (Queue.is_empty queue) && !conflict = None do
    let falsified_lit = Queue.take queue in
    let var = abs falsified_lit in
    let neg = falsified_lit < 0 in
    
    (* Get clauses watching this literal *)
    let watching = 
      match Hashtbl.find_opt solver.watches falsified_lit with
      | Some r -> !r
      | None -> []
    in
    
    let still_watching = ref [] in
    
    List.iter (fun clause_idx ->
      let wc = solver.clauses.(clause_idx) in
      let watch_idx = 
        if get_lit wc wc.watch1 = (var, neg) then wc.watch1
        else wc.watch2
      in
      
      (* Try to find new watch *)
      let found_new = ref false in
      let i = ref 0 in
      let len = List.length wc.lits in
      
      while !i < len && not !found_new do
        if !i <> wc.watch1 && !i <> wc.watch2 then (
          let (v, n) = get_lit wc !i in
          match eval_literal v n state with
          | Some true -> found_new := true  (* satisfied *)
          | None -> found_new := true       (* unassigned *)
          | Some false -> ()                (* falsified, keep looking *)
        );
        if not !found_new then incr i
      done;
      
      if !found_new then (
        (* Update watch *)
        if watch_idx = wc.watch1 then wc.watch1 <- !i
        else wc.watch2 <- !i;
        
        let (new_var, new_neg) = get_lit wc !i in
        let new_key = lit_to_key new_var new_neg in
        let new_list = 
          match Hashtbl.find_opt solver.watches new_key with
          | Some r -> r
          | None -> 
              let r = ref [] in
              Hashtbl.add solver.watches new_key r;
              r
        in
        new_list := clause_idx :: !new_list
      ) else (
        (* Clause is unit or conflict *)
        still_watching := clause_idx :: !still_watching;
        
        let other_idx = if watch_idx = wc.watch1 then wc.watch2 else wc.watch1 in
        let (other_var, other_neg) = get_lit wc other_idx in
        
        match eval_literal other_var other_neg state with
        | Some false -> conflict := Some clause_idx  (* conflict *)
        | None ->  (* unit clause *)
            let value = not other_neg in
            state.value.(other_var) <- Some value;
            state.antecedent.(other_var) <- Some clause_idx;
            state.dl.(other_var) <- current_dl;
            state.phase_saved.(other_var) <- value;
            
            let new_key = lit_to_key other_var (not value) in
            Queue.add new_key queue
        | Some true -> ()  (* already satisfied *)
      )
    ) watching;
    
    (* Update watch list *)
    (match Hashtbl.find_opt solver.watches falsified_lit with
     | Some r -> r := !still_watching
     | None -> ())
  done;
  
  !conflict

(** VSIDS variable selection with phase saving *)
let pick_branching_variable (solver : solver_state) : (int * bool) option =
  let state = solver.state in
  let best_var = ref None in
  let best_score = ref neg_infinity in
  
  for var = 1 to Array.length state.value - 1 do
    if state.value.(var) = None then (
      if state.vsids_activity.(var) > !best_score then (
        best_score := state.vsids_activity.(var);
        best_var := Some var
      )
    )
  done;
  
  match !best_var with
  | None -> None
  | Some var -> Some (var, state.phase_saved.(var))

(** Backtrack to decision level *)
let backtrack (state : state) (b : int) : unit =
  for v = 1 to Array.length state.value - 1 do
    if state.dl.(v) > b then (
      state.value.(v) <- None;
      state.antecedent.(v) <- None;
      state.dl.(v) <- 0
    )
  done

(** Resolve clauses *)
let resolve (clause_a : clause) (clause_b : clause) (x : int) : clause =
  let filtered_a = List.filter (fun (var, _) -> var <> x) clause_a in
  let filtered_b = List.filter (fun (var, _) -> var <> x) clause_b in
  let combined = filtered_a @ filtered_b in
  
  let seen = Hashtbl.create (List.length combined) in
  List.filter (fun lit ->
    if Hashtbl.mem seen lit then false
    else (Hashtbl.add seen lit (); true)
  ) combined

(** First UIP conflict analysis *)
let conflict_analysis (solver : solver_state) (conflict_idx : int) 
    (current_dl : int) : int * clause =
  let state = solver.state in
  
  if current_dl = 0 then
    (-1, solver.clauses.(conflict_idx).lits)
  else
    let current = ref solver.clauses.(conflict_idx).lits in
    
    let rec analyze () =
      let current_level_lits = List.filter (fun (var, _) ->
        state.dl.(var) = current_dl
      ) !current in
      
      (* Bump VSIDS for variables in conflict *)
      List.iter (fun (var, _) -> bump_activity solver var) !current;
      
      if List.length current_level_lits <= 1 then
        !current
      else
        let implied = List.find_opt (fun (var, _) ->
          state.antecedent.(var) <> None
        ) current_level_lits in
        
        match implied with
        | None -> !current
        | Some (var, _) ->
            (match state.antecedent.(var) with
             | Some ant_idx ->
                 let antecedent = solver.clauses.(ant_idx).lits in
                 current := resolve !current antecedent var;
                 analyze ()
             | None -> !current)
    in
    
    let learned = analyze () in
    
    let decision_levels = ref [] in
    List.iter (fun (var, _) ->
      if state.dl.(var) > 0 && not (List.mem state.dl.(var) !decision_levels) then
        decision_levels := state.dl.(var) :: !decision_levels
    ) learned;
    
    let decision_levels = List.sort compare !decision_levels in
    let backtrack_level =
      match List.rev decision_levels with
      | [] -> 0
      | [_] -> 0
      | _ :: b :: _ -> b
      | _ -> 0
    in
    
    (backtrack_level, learned)

(** Main solver with restarts *)
let solve_sat (num_vars : int) (raw_clauses : int list list) 
    : bool option array option =
  let clauses = List.map convert_clause raw_clauses in
  let watched_clauses = Array.of_list (List.map init_watched_clause clauses) in
  
  let state = make_state num_vars in
  let watches = Hashtbl.create (num_vars * 4) in
  
  (* Initialize watch lists *)
  Array.iteri (fun idx wc ->
    let (v1, n1) = get_lit wc wc.watch1 in
    let (v2, n2) = get_lit wc wc.watch2 in
    
    let key1 = lit_to_key v1 n1 in
    let key2 = lit_to_key v2 n2 in
    
    let list1 = match Hashtbl.find_opt watches key1 with
      | Some r -> r
      | None -> let r = ref [] in Hashtbl.add watches key1 r; r
    in
    list1 := idx :: !list1;
    
    if key1 <> key2 then (
      let list2 = match Hashtbl.find_opt watches key2 with
        | Some r -> r
        | None -> let r = ref [] in Hashtbl.add watches key2 r; r
      in
      list2 := idx :: !list2
    )
  ) watched_clauses;
  
  let solver = {
    clauses = watched_clauses;
    watches = watches;
    state = state;
    num_conflicts = 0;
    vsids_inc = vsids_initial_inc;
    vsids_decay = vsids_decay_factor;
  } in
  
  let current_dl = ref 0 in
  let restart_threshold = ref restart_base in
  
  (* Initial propagation *)
  (match unit_propagation solver !current_dl with
   | Some _ -> None
   | None ->
       let rec solve () =
         (* Check restart *)
         if solver.num_conflicts >= !restart_threshold then (
           backtrack state 0;
           current_dl := 0;
           restart_threshold := int_of_float 
             (float !restart_threshold *. restart_inc)
         );
         
         (* Check if all assigned *)
         let all_assigned = ref true in
         for v = 1 to num_vars do
           if state.value.(v) = None then all_assigned := false
         done;
         
         if !all_assigned then Some state.value
         else
           match pick_branching_variable solver with
           | None -> Some state.value
           | Some (var, value) ->
               incr current_dl;
               state.value.(var) <- Some value;
               state.antecedent.(var) <- None;
               state.dl.(var) <- !current_dl;
               
               let rec propagate_and_learn () =
                 match unit_propagation solver !current_dl with
                 | None -> solve ()
                 | Some conflict_idx ->
                     solver.num_conflicts <- solver.num_conflicts + 1;
                     decay_activities solver;
                     
                     let (backtrack_level, learned) =
                       conflict_analysis solver conflict_idx !current_dl in
                     
                     if backtrack_level < 0 then None
                     else (
                       (* Add learned clause *)
                       let new_wc = init_watched_clause learned in
                       let new_idx = Array.length solver.clauses in
                       solver.clauses <- Array.append solver.clauses [|new_wc|];
                       
                       (* Update watches for new clause *)
                       let (v1, n1) = get_lit new_wc new_wc.watch1 in
                       let key1 = lit_to_key v1 n1 in
                       (match Hashtbl.find_opt solver.watches key1 with
                        | Some r -> r := new_idx :: !r
                        | None -> Hashtbl.add solver.watches key1 (ref [new_idx]));
                       
                       if new_wc.watch1 <> new_wc.watch2 then (
                         let (v2, n2) = get_lit new_wc new_wc.watch2 in
                         let key2 = lit_to_key v2 n2 in
                         (match Hashtbl.find_opt solver.watches key2 with
                          | Some r -> r := new_idx :: !r
                          | None -> Hashtbl.add solver.watches key2 (ref [new_idx]))
                       );
                       
                       backtrack state backtrack_level;
                       current_dl := backtrack_level;
                       propagate_and_learn ()
                     )
               in
               propagate_and_learn ()
       in
       solve ()
  )
