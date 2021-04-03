(* RDRAND is a lossless distribution over W64 *)
(* axiom RDRAND_ll : is_lossless RDRAND. *)

require import PwGenDefinitions.

(* rng(n) always outputs something smaller than n *)
lemma rng_n n &m : Pr[RPGSpec.rng(n) @ &m : res < n] = 1%r.
proof.
admit.
qed.


(* passCertPasswordGenerator is correct *)
lemma correctness length lowercase_min lowercase_max uppercase_min uppercase_max numbers_min
    numbers_max special_min special_max &m :
Pr[Correctness.main(length, lowercase_min, lowercase_max, uppercase_min, uppercase_max,
  numbers_min, numbers_max, special_min, special_max) @ &m : res] = 1%r.
proof.
admit.
qed.
