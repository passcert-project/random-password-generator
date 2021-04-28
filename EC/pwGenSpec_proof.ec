require import AllCore IntDiv List UpdateList.

require import PwGenDefinitions PwGenSpec.

(* AUXILIARY LEMMAS *)

(* output of rng is smaller than range*)
lemma rng_h _range :
  hoare [ RPGSpec.rng : 0 < _range /\ range = _range ==> res < _range].
proof.
proc.
wp.
rnd.
skip.
move => &m [H1 H2] r Hr.
rewrite H2.
by apply ltz_pmod.
qed.

(* permutation of a string doesn't change string size*)
lemma permutation_size_hl input:
  hoare [RPGSpec.permutation : string = input ==> size res = size input].
proof.
proc.
seq 1 : (size string = size input).
  auto.
while (size string = size input).
  seq 1 : (size string = size input).
    ecall (rng_h i).
    skip.
    move => />.
  seq 1 : (size string = size input).
    auto.
  seq 1 : (size string = size input).
    auto.
  seq 1 : (size string = size input).
    auto.
    move => &m /> H1.
    by rewrite -size_update.
  auto.
  by rewrite -size_update.
  by skip.
qed.

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
