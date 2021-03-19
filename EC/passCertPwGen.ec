(* RDRAND is a lossless distribution over W64 *)
(* axiom RDRAND_ll : is_lossless RDRAND. *)


(* rng(1) always outputs 0 *)
lemma rng_1 &m : Pr[M.rng(W64.one) @ &m : res \ule W64.zero] = 1%r.
proof.
byphoare. proc.
