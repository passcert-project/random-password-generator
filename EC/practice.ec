require import Core Int IntDiv Distr List.

(* from Jasmin require import JModel.

require import PassCertGenerator_jazz. *)
require import PwGenSpec.

(* RDRAND is a lossless distribution over W64 *)
(* axiom RDRAND_ll : is_lossless RDRAND.

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
*)

lemma rng_h _range :
  hoare [ RPGSpec.rng : range = _range ==> res < _range].
proof.
proc.
wp.
rnd.
skip.
move => &m H r Hr.
rewrite H.
admit.
qed.

lemma constant_string_size ['a] (x:'a) (string:'a list) (i:int):
    i < size string =>
    0 < i =>
    size string = size (insert x string i).
proof.
move => H1 H2.
admit.
qed.

lemma permutation_size_hl input:
  hoare [RPGSpec.permutation : string = input ==> size res = size input].
proof.
proc.
seq 1 : (i = size string). auto.
while (i <= size string /\ size string = size input).
seq 1 : (i <= size string /\ size string = size input /\ j < i).
ecall (rng_h i).
skip.
move => &m [[H1 H2] H3].
split.
reflexivity.
move => H4 result H5.
split.
assumption.
split.
assumption.
assumption.
seq 1 : (i < size string /\ size string = size input /\ j <= i).
auto.
move => &m [H1 [H2 H3]] i.
split.
subst i.

qed.


lemma permutation_size_phl input &m:
    Pr[RPGSpec.permutation(input) @ &m : size res = size input] = 1%r.
proof.
byphoare (_ : (exists m, (size input = m)) ==> size res = size input).
proc.
while ().
qed.
