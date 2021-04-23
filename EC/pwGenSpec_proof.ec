require import AllCore.
require import PwGenDefinitions PwGenSpec.

(* password generator specification is correct *)
lemma correctness length lowercase_min lowercase_max uppercase_min uppercase_max numbers_min
    numbers_max special_min special_max &m :
Pr[Correctness.main(length, lowercase_min, lowercase_max, uppercase_min, uppercase_max,
  numbers_min, numbers_max, special_min, special_max) @ &m : res] = 1%r.
proof.
byphoare.
proc.
seq 1 : (true).
inline CharacterSets.init.
auto.
islossless init.
qed.
