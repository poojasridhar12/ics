(* ================= ENIGMA CONFIGURATION ================= *)

let rotor_wiring = [|
  "EKMFLGDQVZNTOWYHXUSPAIBRCJ";  (* Rotor I *)
  "AJDKSIRUXBLHWTMCQGZNPYFVOE";  (* Rotor II *)
  "BDFHJLCPRTXVZNYEIWGAKMUSQO"   (* Rotor III *)
|]

let notches = [| 'Q'; 'E'; 'V' |]      (* Turnover after these letters for rotors I, II, III *)
let reflector = "YRUHQSLDPXNGOKMIEBFZCWVJAT"

type config = {
  rotors: int list;           (* For example [0;1;2] for I-II-III *)
  positions: int list;        (* Initial positions, 0-based: [0;1;2] for 'A','B','C' *)
  ring_settings: int list;    (* Ring settings, 0-based *)
  plugboard: (char*char) list
}

(* ================== PLUGBOARD ================== *)

let plug_swap pb c =
  try List.assoc c pb with Not_found ->
  try List.assoc c (List.map (fun (a,b)->(b,a)) pb) with Not_found -> c

(* ================== ROTOR: EN/DE ================== *)

let encode_rotor_fwd wiring pos ring input =
  (* Move input through rotor, accounting for position and ring *)
  let step = (input + pos - ring + 26) mod 26 in
  let wired = Char.code wiring.[step] - Char.code 'A' in
  (wired - pos + ring + 26) mod 26

let encode_rotor_bwd wiring pos ring input =
  let step = (input + pos - ring + 26) mod 26 + Char.code 'A' in
  let idx = String.index wiring (Char.chr step) in
  (idx - pos + ring + 26) mod 26

let reflect idx =
  Char.code reflector.[idx] - Char.code 'A'

(* ================== ROTOR STEPPING ================== *)

let notch_at r pos =
  pos = (Char.code notches.(r) - Char.code 'A')

let step_rotors cfg pos =
  match cfg.rotors, pos with
  | [r2;r1;r0], [p2;p1;p0] ->
    (* Rightmost always advances *)
    let p0' = (p0+1) mod 26 in
    (* Handle double-stepping middle rotor when at notch *)
    let turn_middle = notch_at r0 p0' in
    let turn_left   = notch_at r1 p1 in
    let p1' = (p1 + (if turn_middle then 1 else 0)) mod 26 in
    let p2' = (p2 + (if turn_left then 1 else 0)) mod 26 in
    [p2'; p1'; p0']
  | _ -> pos

(* ================== CHARACTER ENCRYPTION ================== *)

let enigma_char cfg positions c =
  if c < 'A' || c > 'Z' then c
  else
    let c1 = plug_swap cfg.plugboard c in
    let idx = Char.code c1 - Char.code 'A' in
    let forward =
      List.fold_left2 (fun acc r p ->
        encode_rotor_fwd rotor_wiring.(r) p (List.nth cfg.ring_settings r) acc
      ) idx cfg.rotors positions
    in
    let refl = reflect forward in
    let backward =
      List.fold_right2 (fun r p acc ->
        encode_rotor_bwd rotor_wiring.(r) p (List.nth cfg.ring_settings r) acc
      ) cfg.rotors positions refl
    in
    plug_swap cfg.plugboard (Char.chr (backward + Char.code 'A'))

let rec enigma_string cfg str =
  let len = String.length str in
  let rec aux idx positions acc =
    if idx = len then String.concat "" (List.rev acc)
    else
      let c = Char.uppercase_ascii str.[idx] in
      let new_positions = step_rotors cfg positions in
      let enc = enigma_char cfg new_positions c in
      aux (idx+1) new_positions ((String.make 1 enc)::acc)
  in
  aux 0 cfg.positions []

(* ============================= EXAMPLE USAGE ============================ *)

let cfg = {
  rotors=[0;1;2];                (* I-II-III *)
  positions=[0;1;2];             (* A=0, B=1, C=2 *)
  ring_settings=[0;0;0];         (* ring settings: A-A-A *)
  plugboard=[('A','Z');('B','D')]
}

let () =
  let text = "HELLOWORLD" in
  let cipher = enigma_string cfg text in
  Printf.printf "Encrypted: %s\n" cipher;

  (* For correct decryption, reset positions *)
  let cfg_reset = {cfg with positions=[0;1;2]} in
  let decrypted = enigma_string cfg_reset cipher in
  Printf.printf "Decrypted: %s\n" decrypted
