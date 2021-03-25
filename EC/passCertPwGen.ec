(* RDRAND is a lossless distribution over W64 *)
(* axiom RDRAND_ll : is_lossless RDRAND. *)

require import passCertGenerator_jazz.

(* rng(1) always outputs 0 *)
lemma rng_1 &m : Pr[M.rng(W64.one) @ &m : res \ule W64.zero] = 1%r.



  (* passCertPasswordGenerator is correct *)
lemma correctness &m : Pr[Correctness.main(policies) @ &m : res] = 1%r.
