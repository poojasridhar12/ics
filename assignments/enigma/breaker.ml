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

(* ================== UPDATE THE BREAK MODE SECTION ================== *)

| "break" ->
    Printf.printf "Mode: Break (Bombe-style)\nCrib: %s\nCipher: %s\n\n" break_crib break_cipher;
    
    (* Validate inputs *)
    if String.length break_crib = 0 || String.length break_cipher = 0 then
      Printf.printf "Error: Crib and cipher must be non-empty\n"
    else (
      (* Remove spaces and validate lengths match *)
      let clean_str s = String.map (fun c -> if c = ' ' then c else c) s 
        |> String.uppercase_ascii in
      let crib_clean = clean_str break_crib in
      let cipher_clean = clean_str break_cipher in
      
      let crib_letters = String.fold_left (fun acc c -> 
        if c >= 'A' && c <= 'Z' then acc + 1 else acc) 0 crib_clean in
      let cipher_letters = String.fold_left (fun acc c -> 
        if c >= 'A' && c <= 'Z' then acc + 1 else acc) 0 cipher_clean in
      
      if crib_letters <> cipher_letters then
        Printf.printf "Error: Crib (%d letters) and cipher (%d letters) must have same length\n" 
          crib_letters cipher_letters
      else (
        Printf.printf "Analyzing with cryptanalytic heuristics...\n";
        
        (* Stage 1: Smart rotor search with pruning *)
        let top_rotors = find_top_rotors_smart break_crib break_cipher 10 in  (* Increase k to 10 *)
        Printf.printf "\nTop %d rotor position candidates:\n" (min 10 (List.length top_rotors));
        
        let shown = ref 0 in
        List.iter (fun (score,pos) ->
          if !shown < 10 then (
            Printf.printf "  Score: %.2f, Position: %s\n" 
              score
              (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
            incr shown
          )
        ) top_rotors;
        
        (* Stage 2: Plugboard search with validation *)
        Printf.printf "\nSearching plugboard configurations...\n";
        let rec search count = function
          | [] -> 
              Printf.printf "\nNo exact match found after testing %d configurations.\n" count;
              Printf.printf "This likely means the cipher was not generated by this Enigma implementation\n";
              Printf.printf "from the given crib with the searched rotor positions and plugboards.\n"
          | (score,pos)::tl ->
              Printf.printf "Testing position %s (score: %.2f)...\n" 
                (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos))
                score;
              match try_plugboards_fast base_cfg break_crib break_cipher pos with
              | None -> search (count + 1) tl
              | Some (pb,cfg_found) ->
                  let decrypted = decrypt_string cfg_found break_cipher in
                  (* Strict validation: decrypted must match crib *)
                  let matches_crib = 
                    let rec check i =
                      if i >= String.length break_crib then true
                      else if i >= String.length decrypted then false
                      else
                        let c1 = Char.uppercase_ascii break_crib.[i] in
                        let c2 = Char.uppercase_ascii decrypted.[i] in
                        if c1 >= 'A' && c1 <= 'Z' && c2 >= 'A' && c2 <= 'Z' then
                          if c1 = c2 then check (i+1) else false
                        else check (i+1)
                    in check 0
                  in
                  
                  if matches_crib then (
                    Printf.printf "\n✓ Configuration Found!\n";
                    Printf.printf "Rotor positions: %s\n" 
                      (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
                    Printf.printf "Plugboard pairs: %s\n" 
                      (if pb = [] then "None" 
                       else String.concat ", " (List.map (fun (a,b) -> Printf.sprintf "%c↔%c" a b) pb));
                    Printf.printf "Decrypted text: %s\n" decrypted
                  ) else (
                    Printf.printf "  Found approximate match but validation failed (decrypted: %s)\n" decrypted;
                    search (count + 1) tl
                  )
        in 
        search 0 top_rotors
      )
    )


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
