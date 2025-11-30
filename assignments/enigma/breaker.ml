(* Configuration *)
let mode = "encrypt"
let text = "HELLOWORLD"
let break_crib = "HELLOWORLD"
let break_cipher = "IGKXQNMDCY" 
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

(* ================== ENIGMA MECHANICS ================== *)

let rotor_wiring = [|
  "EKMFLGDQVZNTOWYHXUSPAIBRCJ";
  "AJDKSIRUXBLHWTMCQGZNPYFVOE";
  "BDFHJLCPRTXVZNYEIWGAKMUSQO"
|]

let reflector = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let notches = [|16; 4; 21|]

let apply_plugboard_map pb c =
  try List.assoc c pb with Not_found ->
  try List.assoc c (List.map (fun (a,b)->(b,a)) pb) with Not_found -> c

let rotor_fwd rotor pos ring input =
  let wiring = rotor_wiring.(rotor-1) in
  let idx = (input + pos - ring + 26) mod 26 in
  (Char.code wiring.[idx] - Char.code 'A' - pos + ring + 26) mod 26

let rotor_bwd rotor pos ring input =
  let wiring = rotor_wiring.(rotor-1) in
  let ch = Char.chr ((input + pos - ring + 26) mod 26 + Char.code 'A') in
  let idx = String.index wiring ch in
  (idx - pos + ring + 26) mod 26

let reflect x = Char.code reflector.[x] - Char.code 'A'

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

let encrypt_char cfg pos c =
  let upper = Char.uppercase_ascii c in
  if not (upper >= 'A' && upper <= 'Z') then c else
  let c = apply_plugboard_map cfg.plugboard upper in
  let input = Char.code c - Char.code 'A' in
  let fwd = List.fold_left2 (fun acc r p -> rotor_fwd r p (List.nth cfg.ring_settings (r-1)) acc) input cfg.rotors pos in
  let refl = reflect fwd in
  let bwd = List.fold_left2 (fun acc r p -> rotor_bwd r p (List.nth cfg.ring_settings (r-1)) acc) refl (List.rev cfg.rotors) (List.rev pos) in
  apply_plugboard_map cfg.plugboard (Char.chr (bwd + Char.code 'A'))

let encrypt_string cfg str =
  if String.length str = 0 then "" else
  let rec aux pos acc chars =
    match chars with
    | [] -> String.concat "" (List.rev acc)
    | ch::tl ->
        let upper = Char.uppercase_ascii ch in
        if upper >= 'A' && upper <= 'Z' then
          let new_pos = advance_rotor_positions cfg.rotors pos in
          let enc = encrypt_char cfg new_pos upper in
          aux new_pos ((String.make 1 enc)::acc) tl
        else
          aux pos ((String.make 1 ch)::acc) tl
  in
  aux cfg.positions [] (List.init (String.length str) (String.get str))

let decrypt_string = encrypt_string

(* ================== CRYPTANALYTIC HEURISTICS ================== *)

let english_freq = [|
  ('E', 12.70); ('T', 9.06); ('A', 8.17); ('O', 7.51); ('I', 6.97);
  ('N', 6.75); ('S', 6.33); ('H', 6.09); ('R', 5.99); ('D', 4.25);
  ('L', 4.03); ('C', 2.78); ('U', 2.76); ('M', 2.41); ('W', 2.36);
  ('F', 2.23); ('G', 2.02); ('Y', 1.97); ('P', 1.93); ('B', 1.29);
  ('V', 0.98); ('K', 0.77); ('J', 0.15); ('X', 0.15); ('Q', 0.10); ('Z', 0.07)
|]

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

let has_plugboard_contradiction pb =
  let rec check_pairs seen = function
    | [] -> false
    | (a,b)::rest ->
        if List.mem a seen || List.mem b seen then true
        else if a = b then true
        else check_pairs (a::b::seen) rest
  in
  check_pairs [] pb

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

let is_impossible_by_crib crib cipher =
  let strip_spaces s = String.fold_left (fun acc c ->
    if c = ' ' then acc else acc ^ String.make 1 c) "" s in
  let crib_clean = strip_spaces (String.uppercase_ascii crib) in
  let cipher_clean = strip_spaces (String.uppercase_ascii cipher) in

  let n = min (String.length crib_clean) (String.length cipher_clean) in
  let rec check i =
    if i >= n then false
    else
      let c_plain = crib_clean.[i] in
      let c_cipher = cipher_clean.[i] in
      if c_plain >= 'A' && c_plain <= 'Z' && c_cipher >= 'A' && c_cipher <= 'Z' then
        if c_plain = c_cipher then true
        else check (i+1)
      else check (i+1)
  in
  check 0

let score_configuration crib cipher test_output =
  let match_score = float_of_int (
    let n = min (String.length test_output) (String.length cipher) in
    let rec aux i acc =
      if i=n then acc
      else aux (i+1) (if test_output.[i]=cipher.[i] then acc+1 else acc)
    in aux 0 0
  ) in

  let freq_score = 1.0 /. (1.0 +. frequency_score test_output) in
  let ic_score = index_of_coincidence test_output in
  let ic_weight = if ic_score > 0.06 then ic_score *. 10.0 else 0.0 in

  (match_score *. 10.0) +. freq_score +. ic_weight

let generate_plugboards_smart crib cipher =
  let letters = List.init 26 (fun i -> Char.chr (i + Char.code 'A')) in

  let likely_pairs = ref [] in
  let strip_spaces s = String.fold_left (fun acc c ->
    if c = ' ' then acc else acc ^ String.make 1 c) "" s in
  let crib_clean = strip_spaces (String.uppercase_ascii crib) in
  let cipher_clean = strip_spaces (String.uppercase_ascii cipher) in

  for i = 0 to min (String.length crib_clean) (String.length cipher_clean) - 1 do
    let c1 = crib_clean.[i] in
    let c2 = cipher_clean.[i] in
    if c1 >= 'A' && c1 <= 'Z' && c2 >= 'A' && c2 <= 'Z' && c1 <> c2 then
      likely_pairs := (c1, c2) :: !likely_pairs
  done;

  let combos = ref [[]] in

  List.iter (fun (a,b) ->
    if not (has_plugboard_contradiction [(a,b)]) then
      combos := [(a,b)] :: !combos
  ) !likely_pairs;

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

  let max_two_pairs = 100 in
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

let try_plugboards_fast cfg crib cipher positions =
  let plugboards = generate_plugboards_smart crib cipher in
  let best_match = ref None in

  List.iter (fun pb ->
    match !best_match with
    | Some _ -> ()
    | None ->
        let cfg_test = { cfg with positions; plugboard=pb } in
        let test_output = encrypt_string cfg_test crib in

        if test_output = cipher then
          best_match := Some (pb, cfg_test)
  ) plugboards;
  !best_match

let find_top_rotors_smart crib cipher k =
  if String.length crib = 0 || String.length cipher = 0 then [] else

  let scored = ref [] in
  let pruned = ref 0 in

  for a=0 to 25 do
    for b=0 to 25 do
      for c=0 to 25 do
        let pos = [a;b;c] in

        if not (is_impossible_by_crib crib cipher) then (
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

  !scored
  |> List.sort (fun (s1,_)(s2,_) -> compare s2 s1)
  |> fun l ->
      let rec take n acc = function
        | [] -> List.rev acc
        | x::xs when n > 0 -> take (n-1) (x::acc) xs
        | _ -> List.rev acc
      in take k [] l

(* ================== MAIN ================== *)

let () =
  match mode with
  | "encrypt" ->
      let output = encrypt_string base_cfg text in
      Printf.printf "Mode: Encrypt\nInput: %s\nOutput: %s\n\n" text output;
      Printf.printf "*** NOW: Copy the output above and use it as break_cipher ***\n";
      Printf.printf "*** THEN: Change mode to \"break\" and run again ***\n"

  | "decrypt" ->
      let output = decrypt_string base_cfg text in
      Printf.printf "Mode: Decrypt\nInput: %s\nOutput: %s\n" text output

  | "break" ->
      Printf.printf "Mode: Break (Bombe-style)\nCrib: %s\nCipher: %s\n\n" break_crib break_cipher;

      if String.length break_crib = 0 || String.length break_cipher = 0 then
        Printf.printf "Error: Crib and cipher must be non-empty\n"
      else (
        let strip_spaces s = String.fold_left (fun acc c ->
          if c = ' ' then acc else acc ^ String.make 1 c) "" s in
        let crib_clean = strip_spaces (String.uppercase_ascii break_crib) in
        let cipher_clean = strip_spaces (String.uppercase_ascii break_cipher) in

        let crib_len = String.length crib_clean in
        let cipher_len = String.length cipher_clean in

        if crib_len <> cipher_len then
          Printf.printf "Error: Crib (%d letters) and cipher (%d letters) must match\n" crib_len cipher_len
        else (
          Printf.printf "Analyzing with cryptanalytic heuristics...\n\n";

          let top_rotors = find_top_rotors_smart break_crib break_cipher 10 in
          Printf.printf "Top %d rotor position candidates:\n" (min 10 (List.length top_rotors));

          let shown = ref 0 in
          List.iter (fun (score,pos) ->
            if !shown < 10 then (
              Printf.printf "  Score: %.2f, Position: %s\n"
                score
                (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
              incr shown
            )
          ) top_rotors;

          Printf.printf "\nSearching plugboard configurations...\n";
          let rec search count = function
            | [] ->
                Printf.printf "\nNo match found after %d tests.\n" count;
                Printf.printf "The cipher was not generated by this Enigma from the crib.\n"
            | (score,pos)::tl ->
                Printf.printf "Testing %s (score: %.2f)...\n"
                  (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos))
                  score;
                match try_plugboards_fast base_cfg break_crib break_cipher pos with
                | None -> search (count + 1) tl
                | Some (pb,cfg_found) ->
                    let decrypted = decrypt_string cfg_found break_cipher in

                    if decrypted = crib_clean then (
                      Printf.printf "\n✓ Configuration Found!\n";
                      Printf.printf "Rotor positions: %s\n"
                        (String.concat "" (List.map (fun x -> String.make 1 (Char.chr (x+65))) pos));
                      Printf.printf "Plugboard: %s\n"
                        (if pb = [] then "None"
                         else String.concat ", " (List.map (fun (a,b) -> Printf.sprintf "%c↔%c" a b) pb));
                      Printf.printf "Decrypted: %s\n" decrypted
                    ) else (
                      Printf.printf "  Approximate match (got: %s)\n" decrypted;
                      search (count + 1) tl
                    )
          in
          search 0 top_rotors
        )
      )

  | _ -> failwith "Invalid mode"
