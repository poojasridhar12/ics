(* The requirement here is to break the code without knowing the settings by taking the encrypted output and testing configurations to find the correct rotor positions and plugboard swaps to decrypt it - Uses the Bombe Algorithm 

Here, I take the paintext and the cipher text and map them, position 0, H is I. Then I taje each rotor position combination and for each position, try to derive plugboard settings. If contradictions need to be found, then they need to be elimanted. *)

