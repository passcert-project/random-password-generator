require import Core Int IntDiv Distr List.

from Jasmin require import JModel.

require import PassCertGenerator_jazz PwGenSpec.

(* RDRAND is a lossless distribution over W64 *)
axiom RDRAND_ll : is_lossless RDRAND.

lemma ule_range (range: int):
 0 < range =>
 forall x, x %% range < range.
proof.
move=> H x.
by apply ltz_pmod.
qed.

lemma rng_h _range : (* {P} S {Q}  --- hoare [ S: P ==> Q ] *)
 hoare [ M.rng : range = (W64.of_int _range) ==> W64.to_uint res < _range].
proof.
proc.
wp.
rnd.
skip.
move => &m H r Hr.
admit.
qed.

lemma rng_ll : islossless M.rng.
proof.
proc; auto => /> *.
apply RDRAND_ll.
qed.

lemma rng_ph _range:
 phoare [ M.rng : range = (W64.of_int _range) ==> W64.to_uint res < _range] = 1%r.
proof.
by conseq rng_ll (rng_h _range).
qed.

lemma rng_equiv:
 equiv [ M.rng ~ M.rng : ={range} ==> ={res} ].
proof.
proc.
admitted.

(* rng(1) always outputs 0 *)
lemma rng_1 range &m :
 Pr[M.rng(W64.of_int range) @ &m : W64.to_uint res < range] = 1%r.
proof.
by byphoare (rng_ph range).
qed.


lemma permutation_size string &m:
    Pr[RPGSpec.permutation(string) @ &m : size res = size string] = 1%r.
proof.
byphoare.
proc.
admit.
auto.
auto.
qed.
