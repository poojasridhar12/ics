(* The requirement here is to break the code without knowing the settings by taking the encrypted output and testing configurations to find the correct rotor positions and plugboard swaps to decrypt it - Uses the Bombe Algorithm 

Here, I take the paintext and the cipher text and map them, position 0, H is I. Then I taje each rotor position combination and for each position, try to derive plugboard settings. If contradictions need to be found, then they need to be elimanted. *)

(* Configuration *)
let mode = "break"  (* "encrypt", "decrypt", or "break" *)
let text = "HELLO WORLD"
let break_crib = "HELLO WLD"
let break_cipher = "KQXDN YPJQ"
let rotors = [1;2;3]
let positions = [0;1;2]
let ring_settings = [0;0;0]
let plugboard = [('A','Z'); ('B','D')]

type config = {
  rotors: int list;
  positions: int list;
  ring_settings: int list;
  plugboard: (char*char) list;
}

let base_cfg = { rotors; positions; ring_settings; plugboard }

(* Enigma *)

let rotor_wiring = [|
  "EKMFLGDQVZNTOWYHXUSPAIBRCJ";
  "AJDKSIRUXBLHWTMCQGZNPYFVOE";
  "BDFHJLCPRTXVZNYEIWGAKMUSQO"
|]

let reflector = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let notches = [|16; 4; 21|]  (* Q, E, V for rotors I, II, III *)

(* Plugboard mapping: returns swapped char or original *)
let apply_plugboard_map pb c =
  try List.assoc c pb with Not_found ->
  try List.assoc c (List.map (fun (a,b)->(b,a)) pb) with Not_found -> c

(* Forward rotor pass *)
let rotor_fwd rotor pos ring input =
  let wiring = rotor_wiring.(rotor-1) in
  let idx = (input + pos - ring + 26) mod 26 in
  (Char.code wiring.[idx] - Char.code 'A' - pos + ring + 26) mod 26

(* Backward rotor pass *)
let rotor_bwd rotor pos ring input =
  let wiring = rotor_wiring.(rotor-1) in
  let ch = Char.chr ((input + pos - ring + 26) mod 26 + Char.code 'A') in
  let idx = String.index wiring ch in
  (idx - pos + ring + 26) mod 26

(* Reflector *)
let reflect x = Char.code reflector.[x] - Char.code 'A'

(* Advance rotors with proper notch behavior *)
let advance_rotor_positions cfg_rotors positions =
  let rec step pos_list rotor_list carry =
    match pos_list, rotor_list with
    | [], [] -> []
    | hd::tl, r::rtl ->
        let notch = notches.(r-1) in
        let next_carry = (hd = notch) in
        let new_hd = (hd + (if carry then 1 else 0)) mod 26 in
        new_hd :: step tl rtl next_carry
    | _ -> pos_list
  in
  List.rev (step (List.rev positions) (List.rev cfg_rotors) true)

(* Encrypt a single character with edge case handling *)
let encrypt_char cfg pos c =
  (* Handle non-letter characters - pass through unchanged *)
  let upper = Char.uppercase_ascii c in
  if not (upper >= 'A' && upper <= 'Z') then c else
  let c = apply_plugboard_map cfg.plugboard upper in
  let input = Char.code c - Char.code 'A' in
  let fwd = List.fold_left2 (fun acc r p -> rotor_fwd r p (List.nth cfg.ring_settings (r-1)) acc) input cfg.rotors pos in
  let refl = reflect fwd in
  let bwd = List.fold_left2 (fun acc r p -> rotor_bwd r p (List.nth cfg.ring_settings (r-1)) acc) refl (List.rev cfg.rotors) (List.rev pos) in
  apply_plugboard_map cfg.plugboard (Char.chr (bwd + Char.code 'A'))

(* Encrypt a string with edge case handling *)
let encrypt_string cfg str =
  (* Handle empty string *)
  if String.length str = 0 then "" else
  let rec aux pos acc chars =
    match chars with
    | [] -> String.concat "" (List.rev acc)
    | ch::tl ->
        let upper = Char.uppercase_ascii ch in
        (* Only advance rotors for letters *)
        if upper >= 'A' && upper <= 'Z' then
          let new_pos = advance_rotor_positions cfg.rotors pos in
          let enc = encrypt_char cfg new_pos upper in
          aux new_pos ((String.make 1 enc)::acc) tl
        else
          (* Pass through non-letters unchanged *)
          aux pos ((String.make 1 ch)::acc) tl
  in
  aux cfg.positions [] (List.init (String.length str) (String.get str))

let decrypt_string = encrypt_string

(* heuristics *)

(* English letter frequency (in order of frequency) *)
let english_freq = [|
  ('E', 12.70); ('T', 9.06); ('A', 8.17); ('O', 7.51); ('I', 6.97);
  ('N', 6.75); ('S', 6.33); ('H', 6.09); ('R', 5.99); ('D', 4.25);
  ('L', 4.03); ('C', 2.78); ('U', 2.76); ('M', 2.41); ('W', 2.36);
  ('F', 2.23); ('G', 2.02); ('Y', 1.97); ('P', 1.93); ('B', 1.29);
  ('V', 0.98); ('K', 0.77); ('J', 0.15); ('X', 0.15); ('Q', 0.10); ('Z', 0.07)
|]

(* Calculate frequency score for text *)
let frequency_score text =
  let counts = Array.make 26 0 in
  String.iter (fun c ->
    let upper = Char.uppercase_ascii c in
    if upper >= 'A' && upper <= 'Z' then
      counts.(Char.code upper - Char.code 'A') <- counts.(Char.code upper - Char.code 'A') + 1
  ) text;
  let total = Array.fold_left (+) 0 counts in
  if total = 0 then 0.0 else
  Array.fold_left (fun acc (ch, expected_freq) ->
    let idx = Char.code ch - Char.code 'A' in
    let actual_freq = (float_of_int counts.(idx)) /. (float_of_int total) *. 100.0 in
    acc +. abs_float (actual_freq -. expected_freq)
  ) 0.0 english_freq

(* Detect contradictions in plugboard assignments *)
let has_plugboard_contradiction pb =
  let rec check_pairs seen = function
    | [] -> false
    | (a,b)::rest ->
        (* Check if either letter already appears *)
        if List.mem a seen || List.mem b seen then true
        (* Check self-loops *)
        else if a = b then true
        else check_pairs (a::b::seen) rest
  in
  check_pairs [] pb

(* Index of Coincidence - measures if text resembles natural language *)
let index_of_coincidence text =
  let counts = Array.make 26 0 in
  let letter_count = ref 0 in
  String.iter (fun c ->
    let upper = Char.uppercase_ascii c in
    if upper >= 'A' && upper <= 'Z' then (
      counts.(Char.code upper - Char.code 'A') <- counts.(Char.code upper - Char.code 'A') + 1;
      incr letter_count
    )
  ) text;
  let n = float_of_int !letter_count in
  if n <= 1.0 then 0.0 else
  Array.fold_left (fun acc count ->
    let fi = float_of_int count in
    acc +. (fi *. (fi -. 1.0))
  ) 0.0 counts /. (n *. (n -. 1.0))

(* Logic *)

(* Advanced scoring combining multiple heuristics *)
let score_configuration crib cipher test_output =
  let match_score = float_of_int (
    let n = min (String.length test_output) (String.length cipher) in
    let rec aux i acc = 
      if i=n then acc 
      else aux (i+1) (if test_output.[i]=cipher.[i] then acc+1 else acc) 
    in aux 0 0
  ) in
  
  (* Weight different factors *)
  let freq_score = 1.0 /. (1.0 +. frequency_score test_output) in
  let ic_score = index_of_coincidence test_output in
  let ic_weight = if ic_score > 0.06 then ic_score *. 10.0 else 0.0 in
  
  (* Combined score favoring exact matches *)
  (match_score *. 10.0) +. freq_score +. ic_weight

(* Crib-based early elimination *)
let is_impossible_by_crib crib cipher positions =
  (* Check for impossible self-encryption (Enigma property: letter never encrypts to itself) *)
  let n = min (String.length crib) (String.length cipher) in
  let rec check i =
    if i >= n then false
    else
      let c_plain = Char.uppercase_ascii crib.[i] in
      let c_cipher = Char.uppercase_ascii cipher.[i] in
      if c_plain >= 'A' && c_plain <= 'Z' && c_cipher >= 'A' && c_cipher <= 'Z' then
        if c_plain = c_cipher then true  (* Impossible! *)
        else check (i+1)
      else check (i+1)
  in
  check 0

(* Generate plugboards more efficiently with constraints *)
let generate_plugboards_smart crib cipher =
  let letters = List.init 26 (fun i -> Char.chr (i + Char.code 'A')) in
  
  (* Extract likely plugboard candidates from crib analysis *)
  let likely_pairs = ref [] in
  for i = 0 to min (String.length crib) (String.length cipher) - 1 do
    let c1 = Char.uppercase_ascii crib.[i] in
    let c2 = Char.uppercase_ascii cipher.[i] in
    if c1 >= 'A' && c1 <= 'Z' && c2 >= 'A' && c2 <= 'Z' && c1 <> c2 then
      likely_pairs := (c1, c2) :: !likely_pairs
  done;
  
  let combos = ref [[]] in
  
  (* Prioritize likely pairs first *)
  List.iter (fun (a,b) ->
    if not (has_plugboard_contradiction [(a,b)]) then
      combos := [(a,b)] :: !combos
  ) !likely_pairs;
  
  (* Generate 1-pair combinations *)
  let rec one_pair = function
    | [] | [_] -> ()
    | x::xs -> 
        List.iter (fun y -> 
          if not (has_plugboard_contradiction [(x,y)]) then
            combos := [(x,y)]::!combos
        ) xs; 
        one_pair xs
  in
  one_pair letters;
  
  (* Generate 2-pair combinations with early termination *)
  let max_two_pairs = 100 in  (* Limit search space *)
  let counter = ref 0 in
  let rec two_pair = function
    | [] | [_] | [_;_] | [_;_;_] -> ()
    | a::rest when !counter < max_two_pairs ->
        List.iter (fun b ->
          if !counter < max_two_pairs then
            let remaining = List.filter (fun c -> c<>a && c<>b) rest in
            let rec choose_cd = function
              | [] | [_] -> ()
              | c::rest3 when !counter < max_two_pairs ->
                  List.iter (fun d -> 
                    if not (has_plugboard_contradiction [(a,b);(c,d)]) then (
                      combos := [(a,b);(c,d)]::!combos;
                      incr counter
                    )
                  ) rest3;
                  choose_cd rest3
              | _ -> ()
            in
            choose_cd remaining
        ) rest;
        two_pair rest
    | _ -> ()
  in
  two_pair letters;
  !combos

(* Try plugboards with early termination *)
let try_plugboards_fast cfg crib cipher positions =
  let plugboards = generate_plugboards_smart crib cipher in
  let best_match = ref None in
  let best_score = ref 0.0 in
  
  List.iter (fun pb ->
    match !best_match with
    | Some _ when !best_score >= float_of_int (String.length crib) -> ()  (* Exact match found *)
    | _ ->
        let cfg_test = { cfg with positions; plugboard=pb } in
        let test_output = encrypt_string cfg_test crib in
        let score = score_configuration crib cipher test_output in
        
        if test_output = cipher then (
          best_match := Some (pb, cfg_test);
          best_score := infinity
        ) else if score > !best_score then (
          best_score := score;
          if score > float_of_int (String.length crib) *. 0.8 then
            best_match := Some (pb, cfg_test)
        )
  ) plugboards;
  !best_match

(* Improved rotor search with early pruning *)
let find_top_rotors_smart crib cipher k =
  (* Handle edge cases *)
  if String.length crib = 0 || String.length cipher = 0 then [] else
  
  let scored = ref [] in
  let pruned = ref 0 in
  
  for a=0 to 25 do 
    for b=0 to 25 do 
      for c=0 to 25 do
        let pos = [a;b;c] in
        
        (* Early elimination: check for impossible configurations *)
        if not (is_impossible_by_crib crib cipher pos) then (
          let cfg_test = { base_cfg with positions=pos; plugboard=[] } in
          let test_output = encrypt_string cfg_test crib in
          let sc = score_configuration crib cipher test_output in
          scored := (sc,pos)::!scored
        ) else
          incr pruned
      done 
    done 
  done;
  
  Printf.printf "Pruned %d impossible configurations\n" !pruned;
  
  (* Sort by score and take top k *)
  !scored 
  |> List.sort (fun (s1,_)(s2,_) -> compare s2 s1) 
  |> fun l -> 
      let rec take n acc = function
        | [] -> List.rev acc
        | x::xs when n > 0 -> take (n-1) (x::acc) xs
        | _ -> List.rev acc
      in take k [] l

(* main code *)
let () =
  match mode with
  | "encrypt" -> 
      let output = encrypt_string base_cfg text in
      Printf.printf "Mode: Encrypt\nInput: %s\nOutput: %s\n" text output
      
  | "decrypt" -> 
      let output = decrypt_string base_cfg text in
      Printf.printf "Mode: Decrypt\nInput: %s\nOutput: %s\n" text output
      
  | "break" ->
      Printf.printf "Mode: Break (Bombe-style)\nCrib: %s\nCipher: %s\n\n" break_crib break_cipher;
      
      (* Handle empty string edge case *)
      if String.length break_crib = 0 || String.length break_cipher = 0 then
        Printf.printf "Error: Crib and cipher must be non-empty\n"
      else (
        Printf.printf "Analyzing with cryptanalytic heuristics...\n";
        
        (* Stage 1: Smart rotor search with pruning *)
        let top_rotors = find_top_rotors_smart break_crib break_cipher 5 in
        Printf.printf "\nTop %d rotor position candidates:\n" (List.length top_rotors);
        List.iter (fun (score,pos) ->
          Printf.printf "  Score: %.2f, Position: %s\n" 
            score
            (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos))
        ) top_rotors;
        
        (* Stage 2: Plugboard search with intelligent pruning *)
        Printf.printf "\nSearching plugboard configurations...\n";
        let rec search = function
          | [] -> Printf.printf "\nNo exact match found (configuration may be outside search space)\n"
          | (score,pos)::tl ->
              Printf.printf "Testing position %s...\n" 
                (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
              match try_plugboards_fast base_cfg break_crib break_cipher pos with
              | None -> search tl
              | Some (pb,cfg_found) ->
                  Printf.printf "\n✓ Configuration Found!\n";
                  Printf.printf "Rotor positions: %s\n" 
                    (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
                  Printf.printf "Plugboard pairs: %s\n" 
                    (if pb = [] then "None" 
                     else String.concat ", " (List.map (fun (a,b) -> Printf.sprintf "%c↔%c" a b) pb));
                  Printf.printf "Decrypted text: %s\n" (decrypt_string cfg_found break_cipher)
        in 
        search top_rotors
      )
      
  | _ -> failwith "Invalid mode: must be 'encrypt', 'decrypt', or 'break'"
