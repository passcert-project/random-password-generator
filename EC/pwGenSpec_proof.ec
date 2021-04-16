(* RDRAND is a lossless distribution over W64 *)
(* axiom RDRAND_ll : is_lossless RDRAND. *)

require import AllCore PwGenDefinitions PwGenSpec.

(* passCertPasswordGenerator is correct *)
lemma correctness length lowercase_min lowercase_max uppercase_min uppercase_max numbers_min
    numbers_max special_min special_max &m :
Pr[Correctness.main(length, lowercase_min, lowercase_max, uppercase_min, uppercase_max,
  numbers_min, numbers_max, special_min, special_max) @ &m : res] = 1%r.
proof.
admit.
qed.
