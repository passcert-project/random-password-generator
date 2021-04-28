require import AllCore IntDiv List.
require import PwGenSpec CharacterSets UpdateList.


(****************************)
(*  CORRECTNESS DEFINITION  *)
(****************************)

(* If, given a concrete password generator, the main procedure of the following module
   is true with 100% probability, then we say that the password generator is correct *)

module Correctness = {


  proc occurrences(password:int list, set:int list) : int = {

    var i, occurrences : int;

    i <- 0;
    occurrences <- 0;

    while (i < size set) {
      occurrences <- occurrences + count (fun (e:int) => (nth 0 set i) = e) password;
      i <- i - 1;
    }
    
    return occurrences;
    
  }

  
  proc satisfiesPolicies(length:int, lowercase_min:int, lowercase_max:int, uppercase_min:int,
  uppercase_max:int, numbers_min:int, numbers_max:int, special_min:int, special_max:int,
  password:int list) : bool = {

    var output : bool;
    var setOccurrences : int;

    output <- true;

    if (!(size password = length)) {
      output <- false;
    }
    setOccurrences <- occurrences(password, CharacterSets.lowercaseLetters);
    if (setOccurrences < lowercase_min || lowercase_max < setOccurrences) {
      output <- false;
    }
    setOccurrences <- occurrences(password, CharacterSets.uppercaseLetters);
    if (setOccurrences < uppercase_min || uppercase_max < setOccurrences) {
      output <- false;
    }
    setOccurrences <- occurrences(password, CharacterSets.numbers);
    if (setOccurrences < numbers_min || numbers_max < setOccurrences) {
      output <- false;
    }
    setOccurrences <- occurrences(password, CharacterSets.specialCharacters);
    if (setOccurrences < special_min || special_max < setOccurrences) {
      output <- false;
    }
    
    return output; 
    
  }
  
  
  proc main(length:int, lowercase_min:int, lowercase_max:int, uppercase_min:int,
  uppercase_max:int, numbers_min:int, numbers_max:int,
  special_min:int, special_max:int) : bool = {
    
    var password : int list;
    var output : bool;
    
    CharacterSets.init();

    password <@ RPGSpec.generate_password(length, lowercase_min, lowercase_max,
    uppercase_min, uppercase_max, numbers_min, numbers_max, special_min, special_max);

    output <@ satisfiesPolicies(length, lowercase_min, lowercase_max, uppercase_min,
    uppercase_max, numbers_min, numbers_max, special_min, special_max, password);

    return output;
    
  }


}.


(**********************)
(*  AUXILIARY LEMMAS  *)
(**********************)

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


(*****************)
(*  MAIN PROOFS  *)
(*****************)

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
