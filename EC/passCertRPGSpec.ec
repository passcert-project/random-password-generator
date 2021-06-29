require import AllCore IntDiv DInterval List UpdateList.
require (****) RPG.

clone include RPG.

module RPGRef : RPG_T = {

  var lowercaseSet, uppercaseSet, numbersSet, specialSet : charSet

  proc rng(range:int) : int = {
    
    var value, maxValue : int;

    maxValue <- ((2^64) %/ range) * range - 1;

    value <$ [0 .. (2^64) - 1];

    while (maxValue < value) {
      value <$ [0 .. (2^64) - 1];
    }
    
    value <- (value %% range);
    
    return value;
    
  }

  
  proc random_char_generator(set:charSet) : char = {
    
    var char : char;
    var choice : int;
    
    choice <@ rng(size set);
    char <- nth (-1) set choice;
    
    return (char);
    
  }

  
  proc permutation(pw:password) : password = {

    var i : int;
    var j : int;
    var aux : char;
    
    i <- size pw;
    
    while (0 < i) {
      j <@ rng(i);
      i <- i - 1;
      aux <- nth 0 pw i;
      pw <- update (nth 0 pw j) pw i;
      pw <- update aux pw j;
    }
    
    return pw;
 
  }


  proc get_lowercase() : charSet = {
    
    var set : charSet;
    set <- [97; 97; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112;
           113; 114; 115; 116; 117; 118; 119; 120; 121; 122];
    return set;

  }


  proc get_uppercase() : charSet = {
    
    var set : charSet;
    set <- [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80; 81; 82; 83; 84; 85;
           86; 87; 88; 89; 90];
    return set;

  }


  proc get_numbers() : charSet = {

    var set : charSet;
    set <- [48; 49; 50; 51; 52; 53; 54; 55; 56; 57];
    return set;

  }


  proc get_special() : charSet = {
    
    var set : charSet;
    set <- [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61];
    return set;

  }


  proc define_union_set(nLowercase:int, nUppercase:int, nNumbers:int, nSpecial:int,
                        lowercaseSet:charSet, uppercaseSet:charSet,
                        numbersSet:charSet, specialSet:charSet) : charSet = {

    var unionSet, set : charSet;

    unionSet <- [];
    
    if (0 < nLowercase) {
      set <- lowercaseSet;
      unionSet <- unionSet ++ set;
    }
    if (0 < nUppercase) {
      set <- uppercaseSet;
      unionSet <- unionSet ++ set;
    }
    if (0 < nNumbers) {
      set <- numbersSet;
      unionSet <- unionSet ++ set;
    }
    if (0 < nSpecial) {
      set <- specialSet;
      unionSet <- unionSet ++ set;
    }

    return unionSet;    

  }

  
  proc generate_password(policy:policy) : password = {

    var generatedPassword : password;
    var unionSet : charSet;
    var randomChar : char;
    var i : int;
    var lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable : int;

    (* initializer sets *)
    lowercaseSet <@ get_lowercase();
    uppercaseSet <@ get_uppercase();
    numbersSet <@ get_numbers();
    specialSet <@ get_special();

    (* initialize random password *)
    generatedPassword <- [];
    
    (* check which sets are available to generate characters from (max > 0) *)

    lowercaseAvailable <- policy.`lowercaseMax;
    uppercaseAvailable <- policy.`uppercaseMax;
    numbersAvailable <- policy.`numbersMax;
    specialAvailable <- policy.`specialMax;

    (* generate characters with min values defined *)     
 
    if (0 < lowercaseAvailable) {
      i <- 0;
      while (i < policy.`lowercaseMin) {
        lowercaseAvailable <- lowercaseAvailable - 1;
        randomChar <@ random_char_generator(lowercaseSet);
        generatedPassword <- generatedPassword ++ [randomChar];
        i <- i + 1;
      }
    }
    if (0 < uppercaseAvailable) {
      i <- 0;
      while (i < policy.`uppercaseMin) {
        uppercaseAvailable <- uppercaseAvailable - 1;
        randomChar <@ random_char_generator(uppercaseSet);
        generatedPassword <- generatedPassword ++ [randomChar];
        i <- i + 1;
      }
    }
    if (0 < numbersAvailable) {
      i <- 0;
      while (i < policy.`numbersMin) {
        numbersAvailable <- numbersAvailable - 1;
        randomChar <@ random_char_generator(numbersSet);
        generatedPassword <- generatedPassword ++ [randomChar];
        i <- i + 1;
      }
    }
    if (0 < specialAvailable) {
      i <- 0;
      while (i < policy.`specialMin) {
        specialAvailable <- specialAvailable - 1;
        randomChar <@ random_char_generator(specialSet);
        generatedPassword <- generatedPassword ++ [randomChar];
        i <- i + 1;
      }
    }

    (* generate characters from the available sets of characters *)

    unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable,
                                 specialAvailable, lowercaseSet, uppercaseSet, numbersSet,
                                 specialSet);

    while (size generatedPassword < policy.`length) {

      randomChar <@ random_char_generator(unionSet);

      if (randomChar \in lowercaseSet) {
        lowercaseAvailable <- lowercaseAvailable - 1;
        if (lowercaseAvailable = 0) {
          unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable,
                                       specialAvailable, lowercaseSet, uppercaseSet, numbersSet,
                                       specialSet);
        }
      }
      elif (randomChar \in uppercaseSet) {
        uppercaseAvailable <- uppercaseAvailable - 1;
        if (uppercaseAvailable = 0) {
          unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable,
                                       specialAvailable, lowercaseSet, uppercaseSet, numbersSet,
                                       specialSet);
        }
      }
      elif (randomChar \in numbersSet) {
        numbersAvailable <- numbersAvailable - 1;
        if (numbersAvailable = 0) {
          unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable,
                                       specialAvailable, lowercaseSet, uppercaseSet, numbersSet,
                                       specialSet);
        }
      }
      elif (randomChar \in specialSet) {
        specialAvailable <- specialAvailable - 1;
        if (specialAvailable = 0) {
          unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable,
                                       specialAvailable, lowercaseSet, uppercaseSet, numbersSet,
                                       specialSet);
        }
      }

      generatedPassword <- generatedPassword ++ [randomChar];

    }

    generatedPassword <@ permutation(generatedPassword);

    return generatedPassword;
    

  }
  
}.



(**********************************)
(*        AUXILIARY LEMMAS        *)
(**********************************)


(* axiom -> rng always terminates *)
axiom rng_ll : islossless RPGRef.rng.


(* output of rng is smaller than range *)
lemma rng_range _range :
  hoare [RPGRef.rng : range = _range /\ 0 < _range ==> 0 <= res /\ res < _range].
proof.
proc.
wp.
seq 1 : (#pre).
  auto.
seq 1 : (#pre /\ 0 <= value).
  auto.
  smt.
while (0 <= value).
  auto.
  smt.
skip.
move => &m /> ? v ? ? ?.
split.
- by apply modn_ge0.
- by apply ltz_pmod. 
qed.



(* input set given to random char generator has the generated char *)
lemma random_char_generator_has _set :
  hoare [RPGRef.random_char_generator : set = _set /\ 0 < size _set ==> res \in _set].
proof.
proc.
auto.
seq 1 : (set = _set /\ 0 <= choice /\ choice < size set).
  ecall (rng_range (size set)).
  auto.
auto.
move => &m [H1 [H2 H3]].
rewrite -H1.
apply mem_nth.
split.
- assumption.
- move => H4.
  assumption.
qed.



(* permutation of a password does not change its size*)
lemma permutation_size input :
  hoare [RPGRef.permutation : pw = input ==> size res = size input].
proof.
proc.
seq 1 : (size pw = size input).
  auto.
while (size pw = size input).
  seq 1 : (size pw = size input).
    ecall (rng_range i).
    skip.
    move => />.
  seq 1 : (size pw = size input).
    auto.
  seq 1 : (size pw = size input).
    auto.
  seq 1 : (size pw = size input).
    auto.
    move => &m /> H1.
    by rewrite -update_size.
  auto.
  by rewrite -update_size.
  by skip.
qed.


(* if the unionSet has characters from a given set, it means that that set is stil 'available'.
   this happens if at least one of the sets is 'available'  *)
lemma unionSet_available
  (_nLowercase, _nUppercase, _nNumbers, _nSpecial:int)
  (_lowercaseSet, _uppercaseSet, _numbersSet, _specialSet:charSet) :
hoare [RPGRef.define_union_set :
         nLowercase = _nLowercase /\
         nUppercase = _nUppercase /\
         nNumbers = _nNumbers /\
         nSpecial = _nSpecial /\
         lowercaseSet = _lowercaseSet /\
         uppercaseSet = _uppercaseSet /\
         numbersSet = _numbersSet /\
         specialSet = _specialSet /\
         0 <= _nLowercase /\
         0 <= _nUppercase /\
         0 <= _nNumbers /\
         0 <= _nSpecial /\
         0 < size _lowercaseSet /\
         0 < size _uppercaseSet /\
         0 < size _numbersSet /\
         0 < size _specialSet /\
         (forall (x : int),
           x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
         (forall (x : int),
           x \in _lowercaseSet => ! (x \in _numbersSet)) /\
         (forall (x : int),
           x \in _lowercaseSet => ! (x \in _specialSet)) /\
         (forall (x : int),
           x \in _uppercaseSet => ! (x \in _numbersSet)) /\
         (forall (x : int),
           x \in _uppercaseSet => ! (x \in _specialSet)) /\
         (forall (x : int),
           x \in _numbersSet => ! (x \in _specialSet))
         ==>
         (0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial => 0 < size res) /\
         (has (fun (x) => x \in res) _lowercaseSet => 0 < _nLowercase) /\
         (has (fun (x) => x \in res) _uppercaseSet => 0 < _nUppercase) /\
         (has (fun (x) => x \in res) _numbersSet => 0 < _nNumbers) /\
         (has (fun (x) => x \in res) _specialSet => 0 < _nSpecial) /\
         (forall x, x \in res => x \in _lowercaseSet \/
                                 x \in _uppercaseSet\/
                                 x \in _numbersSet \/
                                 x \in _specialSet)].
proof.
proc.
seq 1 : (#pre /\ unionSet = []).
  auto.
if.
- seq 2 : (nLowercase = _nLowercase /\
           nUppercase = _nUppercase /\
           nNumbers = _nNumbers /\
           nSpecial = _nSpecial /\
           lowercaseSet = _lowercaseSet /\
           uppercaseSet = _uppercaseSet /\
           numbersSet = _numbersSet /\
           specialSet = _specialSet /\
           0 < size _lowercaseSet /\
           0 < size _uppercaseSet /\
           0 < size _numbersSet /\
           0 < size _specialSet /\
           (forall (x : int),
             x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
           (forall (x : int),
             x \in _lowercaseSet => ! (x \in _numbersSet)) /\
           (forall (x : int),
             x \in _lowercaseSet => ! (x \in _specialSet)) /\
           (forall (x : int),
             x \in _uppercaseSet => ! (x \in _numbersSet)) /\
           (forall (x : int),
             x \in _uppercaseSet => ! (x \in _specialSet)) /\
           (forall (x : int),
             x \in _numbersSet => ! (x \in _specialSet)) /\
           0 < nLowercase /\
           0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
           unionSet = lowercaseSet).
    auto.
    move => />.
    smt(addz_gt0).
  if.
  + seq 2 : (nLowercase = _nLowercase /\
             nUppercase = _nUppercase /\
             nNumbers = _nNumbers /\
             nSpecial = _nSpecial /\
             lowercaseSet = _lowercaseSet /\
             uppercaseSet = _uppercaseSet /\
             numbersSet = _numbersSet /\
             specialSet = _specialSet /\
             0 < size _lowercaseSet /\
             0 < size _uppercaseSet /\
             0 < size _numbersSet /\
             0 < size _specialSet /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _numbersSet)) /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _specialSet)) /\
             (forall (x : int),
               x \in _uppercaseSet => ! (x \in _numbersSet)) /\
             (forall (x : int),
               x \in _uppercaseSet => ! (x \in _specialSet)) /\
             (forall (x : int),
               x \in _numbersSet => ! (x \in _specialSet)) /\
             0 < nLowercase /\
             0 < nUppercase /\
             0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
             unionSet = lowercaseSet ++ uppercaseSet).
      auto.
    if.
    - seq 2 : (nLowercase = _nLowercase /\
               nUppercase = _nUppercase /\
               nNumbers = _nNumbers /\
               nSpecial = _nSpecial /\
               lowercaseSet = _lowercaseSet /\
               uppercaseSet = _uppercaseSet /\
               numbersSet = _numbersSet /\
               specialSet = _specialSet /\
               0 < size _lowercaseSet /\
               0 < size _uppercaseSet /\
               0 < size _numbersSet /\
               0 < size _specialSet /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _numbersSet)) /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _specialSet)) /\
               (forall (x : int),
                 x \in _uppercaseSet => ! (x \in _numbersSet)) /\
               (forall (x : int),
                 x \in _uppercaseSet => ! (x \in _specialSet)) /\
               (forall (x : int),
                 x \in _numbersSet => ! (x \in _specialSet)) /\
               0 < nLowercase /\
               0 < nUppercase /\
               0 < nNumbers /\
               0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
               unionSet = lowercaseSet ++ uppercaseSet ++ numbersSet).
        auto.
      if.
      + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 0 < nLowercase /\
                 0 < nUppercase /\
                 0 < nNumbers /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = lowercaseSet ++ uppercaseSet ++ numbersSet ++ specialSet).
          auto.
          skip.
          smt(size_cat addz_gt0 char_cat2).
      + skip.
        move => />.
        smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat3).
    - if.
      + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 0 < nLowercase /\
                 0 < nUppercase /\
                 !(0 < nNumbers) /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = lowercaseSet ++ uppercaseSet ++ specialSet).
          auto.
          skip.
          move => />.
          smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat3).
       + skip.
         move => &m />.
         smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).
   + if.
     - seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 0 < nLowercase /\
                 0 < nNumbers /\
                 !(0 < nUppercase) /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = lowercaseSet ++ numbersSet).
          auto.
       if.
       + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 0 < nLowercase /\
                 !(0 < nUppercase) /\
                 0 < nNumbers /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = lowercaseSet ++ numbersSet ++ specialSet).
            auto. 
      + skip.
        move => &m />.
        smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat3).
      skip.
      move => &m />.
      smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).
     - if.
       + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 0 < nLowercase /\
                 !(0 < nUppercase) /\
                 !(0 < nNumbers) /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = lowercaseSet ++ specialSet).
            auto.
          skip.
          move => &m />.
          smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).
       + skip.
         move => &m />.
         smt(charset_disjoint_hasnot).
- if.
  + seq 2 : (nLowercase = _nLowercase /\
             nUppercase = _nUppercase /\
             nNumbers = _nNumbers /\
             nSpecial = _nSpecial /\
             lowercaseSet = _lowercaseSet /\
             uppercaseSet = _uppercaseSet /\
             numbersSet = _numbersSet /\
             specialSet = _specialSet /\
             0 < size _lowercaseSet /\
             0 < size _uppercaseSet /\
             0 < size _numbersSet /\
             0 < size _specialSet /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _numbersSet)) /\
             (forall (x : int),
               x \in _lowercaseSet => ! (x \in _specialSet)) /\
             (forall (x : int),
               x \in _uppercaseSet => ! (x \in _numbersSet)) /\
             (forall (x : int),
               x \in _uppercaseSet => ! (x \in _specialSet)) /\
             (forall (x : int),
               x \in _numbersSet => ! (x \in _specialSet)) /\
             !(0 < nLowercase) /\
             0 < nUppercase /\
             0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
             unionSet = uppercaseSet).
      auto.
      move => />.
      smt(addz_gt0).
    if.
    - seq 2 : (nLowercase = _nLowercase /\
               nUppercase = _nUppercase /\
               nNumbers = _nNumbers /\
               nSpecial = _nSpecial /\
               lowercaseSet = _lowercaseSet /\
               uppercaseSet = _uppercaseSet /\
               numbersSet = _numbersSet /\
               specialSet = _specialSet /\
               0 < size _lowercaseSet /\
               0 < size _uppercaseSet /\
               0 < size _numbersSet /\
               0 < size _specialSet /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _numbersSet)) /\
               (forall (x : int),
                 x \in _lowercaseSet => ! (x \in _specialSet)) /\
               (forall (x : int),
                 x \in _uppercaseSet => ! (x \in _numbersSet)) /\
               (forall (x : int),
                 x \in _uppercaseSet => ! (x \in _specialSet)) /\
               (forall (x : int),
                 x \in _numbersSet => ! (x \in _specialSet)) /\
               !(0 < nLowercase) /\
               0 < nUppercase /\
               0 < nNumbers /\
               0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
               unionSet = uppercaseSet ++ numbersSet).
        auto.
      if.
      + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 !(0 < nLowercase) /\
                 0 < nUppercase /\
                 0 < nNumbers /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = uppercaseSet ++ numbersSet ++ specialSet).
          auto.
          skip.
          move => &m />.
          smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat3).
      + skip.
        move => &m />.
        smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).
    - if.
      + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 !(0 < nLowercase) /\
                 0 < nUppercase /\
                 !(0 < nNumbers) /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = uppercaseSet ++ specialSet).
          auto.
          skip.
          move => &m />.
          smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).      
       + skip.
         move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
         smt(charset_disjoint_hasnot).
   + if.
     - seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 !(0 < nLowercase) /\
                 !(0 < nUppercase) /\
                 0 < nNumbers /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = numbersSet).
          auto.
          move => />.
          smt(addz_gt0).
       if.
       + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 !(0 < nLowercase) /\
                 !(0 < nUppercase) /\
                 0 < nNumbers /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = numbersSet ++ specialSet).
            auto.
         skip.
         move => &m />.
         smt(size_cat addz_gt0 disjoint_cat charset_disjoint_hasnot char_cat2).
      + skip.
        move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
        smt(charset_disjoint_hasnot).
     - if.
       + seq 2 : (nLowercase = _nLowercase /\
                 nUppercase = _nUppercase /\
                 nNumbers = _nNumbers /\
                 nSpecial = _nSpecial /\
                 lowercaseSet = _lowercaseSet /\
                 uppercaseSet = _uppercaseSet /\
                 numbersSet = _numbersSet /\
                 specialSet = _specialSet /\
                 0 < size _lowercaseSet /\
                 0 < size _uppercaseSet /\
                 0 < size _numbersSet /\
                 0 < size _specialSet /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _uppercaseSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _lowercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _numbersSet)) /\
                 (forall (x : int),
                   x \in _uppercaseSet => ! (x \in _specialSet)) /\
                 (forall (x : int),
                   x \in _numbersSet => ! (x \in _specialSet)) /\
                 !(0 < nLowercase) /\
                 !(0 < nUppercase) /\
                 !(0 < nNumbers) /\
                 0 < nSpecial /\
                 0 < _nLowercase + _nUppercase + _nNumbers + _nSpecial /\
                 unionSet = specialSet).
            auto.
            move => />.
            smt(addz_gt0).
          skip.
          move => &m />.
          smt(charset_disjoint_hasnot).
       + skip.
         move => /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
         smt tmo=10. (*TODO*)
qed.




(*********************************)
(*          CORRECTNESS          *)
(*********************************)


(* RPG Spec satisfies the length defined in the policy (HL) *)
lemma rpg_correctness_length_hl (p:policy) :
  hoare [RPGRef.generate_password : policy = p /\
         (* assumptions *)
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax
         ==> size res = p.`length].
proof.
proc.
seq 1 : (#pre).
  inline *.
  auto.
seq 1 : (#pre).
  inline *.
  auto.
seq 1 : (#pre).
  inline *.
  auto.
seq 1 : (#pre).
  inline *.
  auto.
seq 1 : ( #pre /\ size generatedPassword = 0).
  auto.
(*seq 1 : (size generatedPassword = 0 /\ #[/:]pre).
  auto.*)
seq 1 : (#[/:]pre /\ lowercaseAvailable = p.`lowercaseMax).
  auto.
seq 1 : (#pre /\ uppercaseAvailable = p.`uppercaseMax).
  auto.
seq 1 : (#pre /\ numbersAvailable = p.`numbersMax).
  auto.
seq 1 : (#pre /\ specialAvailable = p.`specialMax).
  auto.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         uppercaseAvailable = p.`uppercaseMax /\
         numbersAvailable = p.`numbersMax /\
         specialAvailable = p.`specialMax /\
         size generatedPassword = p.`lowercaseMin).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (size generatedPassword = i /\ i <= p.`lowercaseMin /\ policy = p).
      seq 1 : (#pre).
        auto.
      seq 1 : (#pre).
        inline *.
        auto.
        seq 4 : (#pre).
          auto.
        while true.
          auto.
        skip.
        smt.
      auto.
      smt.
      skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         numbersAvailable = p.`numbersMax /\
         specialAvailable = p.`specialMax /\
         size generatedPassword = p.`lowercaseMin + p.`uppercaseMin).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (size generatedPassword = p.`lowercaseMin + i /\ i <= p.`uppercaseMin /\ policy = p).
      seq 1 : (#pre).
        auto.
      seq 1 : (#pre).
        inline *.
        auto.
        seq 4 : (#pre).
          auto.
        while true.
          auto.
        skip.
        smt.
      auto.
      smt.
      skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         specialAvailable = p.`specialMax /\
         size generatedPassword = p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (size generatedPassword = p.`lowercaseMin + p.`uppercaseMin + i /\
           i <= p.`numbersMin /\ policy = p).
      seq 1 : (#pre).
        auto.
      seq 1 : (#pre).
        inline *.
        auto.
        seq 4 : (#pre).
          auto.
        while true.
          auto.
        skip.
        smt.
      auto.
      smt.
      skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         size generatedPassword =
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (size generatedPassword = p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + i /\
           i <= p.`specialMin /\ policy = p).
      seq 1 : (#pre).
        auto.
      seq 1 : (#pre).
        inline *.
        auto.
        seq 4 : (#pre).
          auto.
        while true.
          auto.
        skip.
        smt.
      auto.
      smt.
      skip => /#.
  - skip => /#.
seq 1 : (#pre).
  inline *.
  auto.
seq 1 : (size generatedPassword = p.`length /\ policy = p).
  while (size generatedPassword <= p.`length /\ policy = p).
  seq 1 : (#pre).
    inline *.
    auto.
    seq 4 : (#pre).
      auto.
    while true.
      auto.
    skip.
    smt.
  seq 1 : (#pre).
    if.
    - seq 1 : (#pre).  
        auto.
        if.
        + inline *.
          auto.            
        + skip => /#.
    - if.
      - seq 1 : (#pre).
          auto.
          if.        
          + inline *.
            auto.          
          + skip => /#.
      - if.
        - seq 1 : (#pre).
            auto.
            if.
            + inline *.
              auto.
            + skip => /#.
        - if.
          - seq 1 : (#pre).
            auto.
            if.
            + inline *.
              auto.
            + skip => /# .
    skip.
    smt.
  auto.
  smt.
skip => /#.
ecall (permutation_size generatedPassword).
skip => /#.  
qed.






(* RPGSpec satisfies the different set bounds defined in the policy (HL) *)
lemma rpg_correctness_bounds_hl (p:policy) :
  hoare [RPGRef.generate_password : policy = p /\
         (* assumptions *)
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax
         ==> satisfiesMin p.`lowercaseMin RPGRef.lowercaseSet res /\
             satisfiesMin p.`uppercaseMin RPGRef.uppercaseSet res /\
             satisfiesMin p.`numbersMin RPGRef.numbersSet res /\
             satisfiesMin p.`specialMin RPGRef.specialSet res /\
             satisfiesMax p.`lowercaseMax RPGRef.lowercaseSet res /\
             satisfiesMax p.`uppercaseMax RPGRef.uppercaseSet res /\   
             satisfiesMax p.`numbersMax RPGRef.numbersSet res /\
             satisfiesMax p.`specialMax RPGRef.specialSet res].
proof.
proc.
seq 1 : (#pre /\ 0 < size RPGRef.lowercaseSet /\
         RPGRef.lowercaseSet = [97; 97; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108;
         109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122]).
  inline *.
  auto.
seq 1 : (#pre /\ 0 < size RPGRef.uppercaseSet /\
         RPGRef.uppercaseSet = [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78;
         79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90]).
  inline *.
  auto.
seq 1 : (#pre /\ 0 < size RPGRef.numbersSet /\
         RPGRef.numbersSet = [48; 49; 50; 51; 52; 53; 54; 55; 56; 57]).
  inline *.
  auto.
seq 1 : (#pre /\ 0 < size RPGRef.specialSet /\
         RPGRef.specialSet = [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61]).
  inline *.
  auto.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         size generatedPassword = 0 /\
         0 < size RPGRef.lowercaseSet /\
         0 < size RPGRef.uppercaseSet /\
         0 < size RPGRef.numbersSet /\
         0 < size RPGRef.specialSet /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
         setOccurrences RPGRef.lowercaseSet generatedPassword = 0 /\
         setOccurrences RPGRef.uppercaseSet generatedPassword = 0 /\
         setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
         setOccurrences RPGRef.specialSet generatedPassword = 0).
  auto.
  move => &m />.
  smt.
seq 1 : (#pre /\
         lowercaseAvailable = p.`lowercaseMax /\
         setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
           p.`lowercaseMax).
  auto.
  move => &m />. 
  smt.
seq 1 : (#pre /\
         uppercaseAvailable = p.`uppercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
           p.`uppercaseMax).
  auto.
  move => &m />.
  smt.
seq 1 : (#pre /\
         numbersAvailable = p.`numbersMax /\
         setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
           p.`numbersMax).
  auto.
  move => &m />.
  smt.
seq 1 : (#pre /\
         specialAvailable = p.`specialMax /\
         setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
           p.`specialMax).
  auto.
  move => &m />.
  smt.
seq 0 : (#pre /\
         p.`length <=
           (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
           size generatedPassword).
  auto.
  smt.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         0 < size RPGRef.lowercaseSet /\
         0 < size RPGRef.uppercaseSet /\
         0 < size RPGRef.numbersSet /\
         0 < size RPGRef.specialSet /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
         lowercaseAvailable <= p.`lowercaseMax /\
         uppercaseAvailable = p.`uppercaseMax /\
         numbersAvailable = p.`numbersMax /\
         specialAvailable = p.`specialMax /\
         p.`length <=
           (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
           size generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
         setOccurrences RPGRef.uppercaseSet generatedPassword = 0 /\
         setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
         setOccurrences RPGRef.specialSet generatedPassword = 0 /\
         setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
           p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
           p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
           p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
           p.`specialMax).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (policy = p /\
           0 < size RPGRef.lowercaseSet /\
           0 < size RPGRef.uppercaseSet /\
           0 < size RPGRef.numbersSet /\
           0 < size RPGRef.specialSet /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
           lowercaseAvailable = p.`lowercaseMax - i /\
           p.`length <=
             (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
             size generatedPassword /\
           setOccurrences RPGRef.lowercaseSet generatedPassword = i /\
           setOccurrences RPGRef.uppercaseSet generatedPassword = 0 /\
           setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
           setOccurrences RPGRef.specialSet generatedPassword = 0 /\
           setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
             p.`lowercaseMax /\
           setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
             p.`uppercaseMax /\
           setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
             p.`numbersMax /\
           setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
             p.`specialMax /\
           i <= p.`lowercaseMin).
    + seq 1 : (policy = p /\
               0 < size RPGRef.lowercaseSet /\
               0 < size RPGRef.uppercaseSet /\
               0 < size RPGRef.numbersSet /\
               0 < size RPGRef.specialSet /\              
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
               lowercaseAvailable = (p.`lowercaseMax - i) - 1 /\
               p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                 size generatedPassword + 1 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword = i /\
               setOccurrences RPGRef.uppercaseSet generatedPassword = 0 /\
               setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
               setOccurrences RPGRef.specialSet generatedPassword = 0 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable + 1 =
                 p.`lowercaseMax /\
               setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                 p.`uppercaseMax /\
               setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                 p.`numbersMax /\
               setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                 p.`specialMax /\
               i < policy.`lowercaseMin).
        auto.
        move => &m />.
        smt.
      seq 1 : (#pre /\ randomChar \in RPGRef.lowercaseSet /\
             !(randomChar \in RPGRef.uppercaseSet) /\
             !(randomChar \in RPGRef.numbersSet) /\
             !(randomChar \in RPGRef.specialSet)).
        ecall (random_char_generator_has RPGRef.lowercaseSet).
        skip.
        move => &m />.
        smt.
      auto.
      move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
      split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
    + skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         0 < size RPGRef.lowercaseSet /\
         0 < size RPGRef.uppercaseSet /\
         0 < size RPGRef.numbersSet /\
         0 < size RPGRef.specialSet /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
         lowercaseAvailable <= p.`lowercaseMax /\
         uppercaseAvailable <= p.`uppercaseMax /\
         numbersAvailable = p.`numbersMax /\
         specialAvailable = p.`specialMax /\
         p.`length <=
           (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
           size generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
         setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
         setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
         setOccurrences RPGRef.specialSet generatedPassword = 0 /\
         setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
           p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
           p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
           p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
           p.`specialMax).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (policy = p /\
           0 < size RPGRef.lowercaseSet /\
           0 < size RPGRef.uppercaseSet /\
           0 < size RPGRef.numbersSet /\
           0 < size RPGRef.specialSet /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
           lowercaseAvailable <= p.`lowercaseMax /\
           uppercaseAvailable = p.`uppercaseMax - i /\
           p.`length <=
             (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
             size generatedPassword /\
           setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
           setOccurrences RPGRef.uppercaseSet generatedPassword = i /\
           setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
           setOccurrences RPGRef.specialSet generatedPassword = 0 /\
           setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
             p.`lowercaseMax /\
           setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
             p.`uppercaseMax /\
           setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
             p.`numbersMax /\
           setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
             p.`specialMax /\
           i <= p.`uppercaseMin).
    + seq 1 : (policy = p /\
               (* derived from the program *)
               0 < size RPGRef.lowercaseSet /\
               0 < size RPGRef.uppercaseSet /\
               0 < size RPGRef.numbersSet /\
               0 < size RPGRef.specialSet /\              
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
               lowercaseAvailable <= p.`lowercaseMax /\
               uppercaseAvailable = (p.`uppercaseMax - i) - 1 /\
               p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                 size generatedPassword + 1 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
               setOccurrences RPGRef.uppercaseSet generatedPassword = i /\
               setOccurrences RPGRef.numbersSet generatedPassword = 0 /\
               setOccurrences RPGRef.specialSet generatedPassword = 0 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                 p.`lowercaseMax /\
               setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable + 1 =
                 p.`uppercaseMax /\
               setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                 p.`numbersMax /\
               setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                 p.`specialMax /\
               i < policy.`uppercaseMin).
        auto.
        move => &m />.
        smt.
      seq 1 : (#pre /\ randomChar \in RPGRef.uppercaseSet /\
             !(randomChar \in RPGRef.lowercaseSet) /\
             !(randomChar \in RPGRef.numbersSet) /\
             !(randomChar \in RPGRef.specialSet)).
        ecall (random_char_generator_has RPGRef.uppercaseSet).
        skip.
        move => &m />.
        smt.
      auto.
      move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
      split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
    + skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         0 < size RPGRef.lowercaseSet /\
         0 < size RPGRef.uppercaseSet /\
         0 < size RPGRef.numbersSet /\
         0 < size RPGRef.specialSet /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
         lowercaseAvailable <= p.`lowercaseMax /\
         uppercaseAvailable <= p.`uppercaseMax /\
         numbersAvailable <= p.`numbersMax /\
         specialAvailable = p.`specialMax /\
         p.`length <=
           (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
           size generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
         setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
         setOccurrences RPGRef.numbersSet generatedPassword = p.`numbersMin /\
         setOccurrences RPGRef.specialSet generatedPassword = 0 /\
         setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
           p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
           p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
           p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
           p.`specialMax).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (policy = p /\
           0 < size RPGRef.lowercaseSet /\
           0 < size RPGRef.uppercaseSet /\
           0 < size RPGRef.numbersSet /\
           0 < size RPGRef.specialSet /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
           lowercaseAvailable <= p.`lowercaseMax /\
           uppercaseAvailable <= p.`uppercaseMax /\
           numbersAvailable = p.`numbersMax - i /\
           p.`length <=
             (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
             size generatedPassword /\
           setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
           setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
           setOccurrences RPGRef.numbersSet generatedPassword = i /\
           setOccurrences RPGRef.specialSet generatedPassword = 0 /\
           setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
             p.`lowercaseMax /\
           setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
             p.`uppercaseMax /\
           setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
             p.`numbersMax /\
           setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
             p.`specialMax /\
           i <= p.`numbersMin).
    + seq 1 : (policy = p /\
               (* derived from the program *)
               0 < size RPGRef.lowercaseSet /\
               0 < size RPGRef.uppercaseSet /\
               0 < size RPGRef.numbersSet /\
               0 < size RPGRef.specialSet /\              
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
               lowercaseAvailable <= p.`lowercaseMax /\
               uppercaseAvailable <= p.`uppercaseMax /\
               numbersAvailable = (p.`numbersMax - i) - 1 /\
               p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                 size generatedPassword + 1 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
               setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
               setOccurrences RPGRef.numbersSet generatedPassword = i /\
               setOccurrences RPGRef.specialSet generatedPassword = 0 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                 p.`lowercaseMax /\
               setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                 p.`uppercaseMax /\
               setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable + 1 =
                 p.`numbersMax /\
               setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                 p.`specialMax /\
               i < policy.`numbersMin).
        auto.
        move => &m />.
        smt.
      seq 1 : (#pre /\ randomChar \in RPGRef.numbersSet /\
             !(randomChar \in RPGRef.lowercaseSet) /\
             !(randomChar \in RPGRef.uppercaseSet) /\
             !(randomChar \in RPGRef.specialSet)).
        ecall (random_char_generator_has RPGRef.numbersSet).
        skip.
        move => &m />.
        smt.
      auto.
      move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
      split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
    + skip => /#.
  - skip => /#.
seq 1 : (policy = p /\
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax /\
         0 < size RPGRef.lowercaseSet /\
         0 < size RPGRef.uppercaseSet /\
         0 < size RPGRef.numbersSet /\
         0 < size RPGRef.specialSet /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
         (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
         (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
         lowercaseAvailable <= p.`lowercaseMax /\
         uppercaseAvailable <= p.`uppercaseMax /\
         numbersAvailable <= p.`numbersMax /\
         specialAvailable <= p.`specialMax /\
         p.`length <=
           (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
           size generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
         setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
         setOccurrences RPGRef.numbersSet generatedPassword = p.`numbersMin /\
         setOccurrences RPGRef.specialSet generatedPassword = p.`specialMin /\
         setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
           p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
           p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
           p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
           p.`specialMax).
  if.
  - seq 1 : (#pre /\ i = 0).
      auto.
    while (policy = p /\
           0 < size RPGRef.lowercaseSet /\
           0 < size RPGRef.uppercaseSet /\
           0 < size RPGRef.numbersSet /\
           0 < size RPGRef.specialSet /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
           (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
           (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
           lowercaseAvailable <= p.`lowercaseMax /\
           uppercaseAvailable <= p.`uppercaseMax /\
           numbersAvailable <= p.`numbersMax /\
           specialAvailable = p.`specialMax - i /\
           p.`length <=
             (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
             size generatedPassword /\
           setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
           setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
           setOccurrences RPGRef.numbersSet generatedPassword = p.`numbersMin /\
           setOccurrences RPGRef.specialSet generatedPassword = i /\
           setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
             p.`lowercaseMax /\
           setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
             p.`uppercaseMax /\
           setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
             p.`numbersMax /\
           setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
             p.`specialMax /\
           i <= p.`specialMin).
    + seq 1 : (policy = p /\
               0 < size RPGRef.lowercaseSet /\
               0 < size RPGRef.uppercaseSet /\
               0 < size RPGRef.numbersSet /\
               0 < size RPGRef.specialSet /\              
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
               (forall (x), x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
               (forall (x), x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
               lowercaseAvailable <= p.`lowercaseMax /\
               uppercaseAvailable <= p.`uppercaseMax /\
               numbersAvailable <= p.`numbersMax /\
               specialAvailable = (p.`specialMax - i) - 1 /\
               p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                 size generatedPassword + 1 /\
               setOccurrences RPGRef.lowercaseSet generatedPassword = p.`lowercaseMin /\
               setOccurrences RPGRef.uppercaseSet generatedPassword = p.`uppercaseMin /\
               setOccurrences RPGRef.numbersSet generatedPassword = p.`numbersMin /\
               setOccurrences RPGRef.specialSet generatedPassword = i /\
               setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                 p.`lowercaseMax /\
               setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                 p.`uppercaseMax /\
               setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                 p.`numbersMax /\
               setOccurrences RPGRef.specialSet generatedPassword + specialAvailable + 1 =
                 p.`specialMax /\
               i < policy.`specialMin).
        auto.
        move => &m />.
        smt.
      seq 1 : (#pre /\ randomChar \in RPGRef.specialSet /\
             !(randomChar \in RPGRef.lowercaseSet) /\
             !(randomChar \in RPGRef.uppercaseSet) /\
             !(randomChar \in RPGRef.numbersSet)).
        ecall (random_char_generator_has RPGRef.specialSet).
        skip.
        move => &m />.
        smt.
      auto.
      move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
      split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
    + skip => /#.
  - skip => /#.
seq 1 : (#pre /\
         (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable =>
            0 < size unionSet) /\
         (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
         (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
         (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
         (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
         (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet)).
  ecall (unionSet_available lowercaseAvailable uppercaseAvailable numbersAvailable
                             specialAvailable RPGRef.lowercaseSet RPGRef.uppercaseSet
                             RPGRef.numbersSet RPGRef.specialSet).
  skip.
  move => &m />.
  smt.
seq 1 : (policy = p /\
         p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
         p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
         p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
         p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
while (policy = p /\
       p.`lowercaseMin <= p.`lowercaseMax /\
       p.`uppercaseMin <= p.`uppercaseMax /\
       p.`numbersMin <= p.`numbersMax /\
       p.`specialMin <= p.`specialMax /\
       0 < size RPGRef.lowercaseSet /\
       0 < size RPGRef.uppercaseSet /\
       0 < size RPGRef.numbersSet /\
       0 < size RPGRef.specialSet /\
       (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
       (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
       (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
       (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
       (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
       (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
       0 <= lowercaseAvailable /\
       0 <= uppercaseAvailable/\
       0 <= numbersAvailable /\
       0 <= specialAvailable /\
       (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable
         => 0 < size unionSet) /\
       (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
       (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
       (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
       (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
       (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
       p.`length <=
         (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
         size generatedPassword /\
       setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
         p.`lowercaseMax /\
       setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
         p.`uppercaseMax /\
       setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
         p.`numbersMax /\
       setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
         p.`specialMax /\
       p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
       p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
       p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
       p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
       setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
       setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
       setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
       setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
- seq 0 : (#pre /\
           0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable).
    skip.
    move => &m />.
    smt.
  seq 1 : (#pre /\ randomChar \in unionSet).
    ecall (random_char_generator_has unionSet).
    skip.
    move => &m />.    
  if.
  + seq 2 : (policy = p /\
             randomChar \in RPGRef.lowercaseSet /\
             0 < size RPGRef.lowercaseSet /\
             0 < size RPGRef.uppercaseSet /\
             0 < size RPGRef.numbersSet /\
             0 < size RPGRef.specialSet /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
             0 <= lowercaseAvailable /\
             0 <= uppercaseAvailable /\
             0 <= numbersAvailable /\
             0 <= specialAvailable /\
             (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable
                => 0 < size unionSet) /\
             (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
             (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
             p.`length <=
               (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
               size generatedPassword + 1 /\
             setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable + 1 =
               p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
               p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
               p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
               p.`specialMax /\
             p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
             p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
             p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
             p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
             setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
      case (1 < lowercaseAvailable).
      - seq 1 : (policy = p /\
                 randomChar \in RPGRef.lowercaseSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 < lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
               (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
               (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
               (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
               (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
               (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                  (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable)+
                   size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable + 1 =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
        if.
        + conseq (_ : false ==> _).
          smt.
          auto.
        + skip => /#.
      - seq 1 : (policy = p /\
                 randomChar \in RPGRef.lowercaseSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 = lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
               (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
               (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
               (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
               (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                  size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable + 1 =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
      if.
      + ecall (unionSet_available lowercaseAvailable uppercaseAvailable numbersAvailable
                                  specialAvailable RPGRef.lowercaseSet RPGRef.uppercaseSet
                                  RPGRef.numbersSet RPGRef.specialSet).
        by skip.
      + by skip.
    auto.
    move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
+ if.
  - seq 2 : (policy = p /\
             randomChar \in RPGRef.uppercaseSet /\
             0 < size RPGRef.lowercaseSet /\
             0 < size RPGRef.uppercaseSet /\
             0 < size RPGRef.numbersSet /\
             0 < size RPGRef.specialSet /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
             0 <= lowercaseAvailable /\
             0 <= uppercaseAvailable /\
             0 <= numbersAvailable /\
             0 <= specialAvailable /\
             (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable
                => 0 < size unionSet) /\
             (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
             (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
             p.`length <=
               (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
               size generatedPassword + 1 /\
             setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
               p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable + 1 =
               p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
               p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
               p.`specialMax /\
             p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
             p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
             p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
             p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
             setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
      case (1 < uppercaseAvailable).
      + seq 1 : (policy = p /\
                 randomChar \in RPGRef.uppercaseSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 < uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                  (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable)+
                   size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable + 1 =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
        if.
        - conseq (_ : false ==> _).
          smt.
          auto.
        - skip => /#.
      + seq 1 : (policy = p /\
                 randomChar \in RPGRef.uppercaseSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 = uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                  size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable + 1 =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
      if.
      - ecall (unionSet_available lowercaseAvailable uppercaseAvailable numbersAvailable
                                  specialAvailable RPGRef.lowercaseSet RPGRef.uppercaseSet
                                  RPGRef.numbersSet RPGRef.specialSet).
        by skip.
      - by skip.
    auto.
    move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
- if.
  + seq 2 : (policy = p /\
             randomChar \in RPGRef.numbersSet /\
             0 < size RPGRef.lowercaseSet /\
             0 < size RPGRef.uppercaseSet /\
             0 < size RPGRef.numbersSet /\
             0 < size RPGRef.specialSet /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
             0 <= lowercaseAvailable /\
             0 <= uppercaseAvailable /\
             0 <= numbersAvailable /\
             0 <= specialAvailable /\
             (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable
                => 0 < size unionSet) /\
             (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
             (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
             p.`length <=
               (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
               size generatedPassword + 1 /\
             setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
               p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
               p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable + 1 =
               p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
               p.`specialMax /\
             p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
             p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
             p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
             p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
             setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
      case (1 < numbersAvailable).
      - seq 1 : (policy = p /\
                 randomChar \in RPGRef.numbersSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 < numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                  (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable)+
                   size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable + 1 =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
        if.
        + conseq (_ : false ==> _).
          smt.
          auto.
        + skip => /#.
      - seq 1 : (policy = p /\
                 randomChar \in RPGRef.numbersSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 = numbersAvailable /\
                 0 <= specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                  size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable + 1 =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
      if.
      + ecall (unionSet_available lowercaseAvailable uppercaseAvailable numbersAvailable
                                  specialAvailable RPGRef.lowercaseSet RPGRef.uppercaseSet
                                  RPGRef.numbersSet RPGRef.specialSet).
        by skip.
      + by skip.
    auto.
    move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
+ if.
  - seq 2 : (policy = p /\
             randomChar \in RPGRef.specialSet /\
             0 < size RPGRef.lowercaseSet /\
             0 < size RPGRef.uppercaseSet /\
             0 < size RPGRef.numbersSet /\
             0 < size RPGRef.specialSet /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
             (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
             (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
             0 <= lowercaseAvailable /\
             0 <= uppercaseAvailable /\
             0 <= numbersAvailable /\
             0 <= specialAvailable /\
             (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable
                => 0 < size unionSet) /\
             (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
             (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
             (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
             p.`length <=
               (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
               size generatedPassword + 1 /\
             setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
               p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
               p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
               p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword + specialAvailable + 1 =
               p.`specialMax /\
             p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
             p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
             p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
             p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
             setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
             setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
             setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
             setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
      case (1 < specialAvailable).
      + seq 1 : (policy = p /\
                 randomChar \in RPGRef.specialSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 < specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.specialSet => 0 < specialAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                  (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable)+
                   size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable + 1 =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
        if.
        - conseq (_ : false ==> _).
          smt.
          auto.
        - skip => /#.
      + seq 1 : (policy = p /\
                 randomChar \in RPGRef.specialSet /\
                 0 < size RPGRef.lowercaseSet /\
                 0 < size RPGRef.uppercaseSet /\
                 0 < size RPGRef.numbersSet /\
                 0 < size RPGRef.specialSet /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.uppercaseSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.lowercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.numbersSet)) /\
                 (forall x, x \in RPGRef.uppercaseSet => !(x \in RPGRef.specialSet)) /\
                 (forall x, x \in RPGRef.numbersSet => !(x \in RPGRef.specialSet)) /\
                 0 <= lowercaseAvailable /\
                 0 <= uppercaseAvailable /\
                 0 <= numbersAvailable /\
                 0 = specialAvailable /\
                 (0 < lowercaseAvailable + uppercaseAvailable + numbersAvailable +
                   specialAvailable => 0 < size unionSet) /\
                (has (fun (x) => x \in unionSet) RPGRef.lowercaseSet => 0 < lowercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.uppercaseSet => 0 < uppercaseAvailable) /\
                (has (fun (x) => x \in unionSet) RPGRef.numbersSet => 0 < numbersAvailable) /\
                (forall x, x \in unionSet => x \in RPGRef.lowercaseSet \/
                                 x \in RPGRef.uppercaseSet\/
                                 x \in RPGRef.numbersSet \/
                                 x \in RPGRef.specialSet) /\
                p.`length <=
                 (lowercaseAvailable + uppercaseAvailable + numbersAvailable + specialAvailable) +
                  size generatedPassword + 1 /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword + lowercaseAvailable =
                   p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword + uppercaseAvailable =
                   p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword + numbersAvailable =
                   p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword + specialAvailable + 1 =
                   p.`specialMax /\
                 p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
                 p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
                 p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
                 p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
                 setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
                 setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
                 setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
                 setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax).
          auto.
          move => &m />.
          smt.
      if.
      - ecall (unionSet_available lowercaseAvailable uppercaseAvailable numbersAvailable
                                  specialAvailable RPGRef.lowercaseSet RPGRef.uppercaseSet
                                  RPGRef.numbersSet RPGRef.specialSet).
        by skip.
      - by skip.
    auto.
    move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. split. smt. smt.
conseq (_: false ==> _).
  + move => &m />.
    smt.
  + auto.
- skip.
  move => &m />.
  smt.
inline RPGRef.permutation.
seq 2 : (#pre /\
         i0 = size pw /\
         setOccurrences RPGRef.lowercaseSet generatedPassword =
         setOccurrences RPGRef.lowercaseSet pw /\
         setOccurrences RPGRef.uppercaseSet generatedPassword =
         setOccurrences RPGRef.uppercaseSet pw /\
         setOccurrences RPGRef.numbersSet generatedPassword =
         setOccurrences RPGRef.numbersSet pw /\
         setOccurrences RPGRef.specialSet generatedPassword =
         setOccurrences RPGRef.specialSet pw).
auto.
seq 1 : (policy = p /\
         p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
         p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
         p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
         p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax /\
         setOccurrences RPGRef.lowercaseSet generatedPassword =
         setOccurrences RPGRef.lowercaseSet pw /\
         setOccurrences RPGRef.uppercaseSet generatedPassword =
         setOccurrences RPGRef.uppercaseSet pw /\
         setOccurrences RPGRef.numbersSet generatedPassword =
         setOccurrences RPGRef.numbersSet pw /\
         setOccurrences RPGRef.specialSet generatedPassword =
         setOccurrences RPGRef.specialSet pw).
  while (policy = p /\
         p.`lowercaseMin <= setOccurrences RPGRef.lowercaseSet generatedPassword /\
         p.`uppercaseMin <= setOccurrences RPGRef.uppercaseSet generatedPassword /\
         p.`numbersMin <= setOccurrences RPGRef.numbersSet generatedPassword /\
         p.`specialMin <= setOccurrences RPGRef.specialSet generatedPassword /\
         setOccurrences RPGRef.lowercaseSet generatedPassword <= p.`lowercaseMax /\
         setOccurrences RPGRef.uppercaseSet generatedPassword <= p.`uppercaseMax /\
         setOccurrences RPGRef.numbersSet generatedPassword <= p.`numbersMax /\
         setOccurrences RPGRef.specialSet generatedPassword <= p.`specialMax /\
         i0 <= size pw /\
         setOccurrences RPGRef.lowercaseSet generatedPassword =
         setOccurrences RPGRef.lowercaseSet pw /\
         setOccurrences RPGRef.uppercaseSet generatedPassword =
         setOccurrences RPGRef.uppercaseSet pw /\
         setOccurrences RPGRef.numbersSet generatedPassword =
         setOccurrences RPGRef.numbersSet pw /\
         setOccurrences RPGRef.specialSet generatedPassword =
         setOccurrences RPGRef.specialSet pw).
  - seq 1 : (#pre /\ j < i0 /\ 0 <= j).
      ecall (rng_range i0).
      skip => /#.
    auto.
    move => &m /> ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?.
    split.
    rewrite -update_size.
    rewrite -update_size.
    smt.
    split.
    rewrite setocc_swap; do! assumption.
    split.
    rewrite setocc_swap; do! assumption.
    split.
    rewrite setocc_swap; do! assumption.
    rewrite setocc_swap; do! assumption.
  - by skip.
auto.
smt.
qed.



(* RPGSpec satisfies both the length and the bounds defined in the policy *)
lemma rpg_correctness_hl (p:policy) :
  hoare [RPGRef.generate_password : policy = p /\
         (* assumptions *)
         p.`length <= 200 /\
         0 < p.`length /\ 
         0 <= p.`lowercaseMin /\
         0 <= p.`uppercaseMin /\
         0 <= p.`numbersMin /\
         0 <= p.`specialMin /\
         0 <= p.`lowercaseMax /\
         0 <= p.`uppercaseMax /\
         0 <= p.`numbersMax /\
         0 <= p.`specialMax /\
         p.`lowercaseMin <= p.`lowercaseMax /\
         p.`uppercaseMin <= p.`uppercaseMax /\
         p.`numbersMin <= p.`numbersMax /\
         p.`specialMin <= p.`specialMax /\
         p.`lowercaseMin + p.`uppercaseMin + p.`numbersMin + p.`specialMin <= p.`length /\
         p.`length <= p.`lowercaseMax + p.`uppercaseMax + p.`numbersMax + p.`specialMax
         ==> size res = p.`length /\
             satisfiesMin p.`lowercaseMin RPGRef.lowercaseSet res /\
             satisfiesMax p.`lowercaseMax RPGRef.lowercaseSet res /\
             satisfiesMin p.`uppercaseMin RPGRef.uppercaseSet res /\
             satisfiesMax p.`uppercaseMax RPGRef.uppercaseSet res /\
             satisfiesMin p.`numbersMin RPGRef.numbersSet res /\
             satisfiesMax p.`numbersMax RPGRef.numbersSet res /\
             satisfiesMin p.`specialMin RPGRef.specialSet res /\
             satisfiesMax p.`specialMax RPGRef.specialSet res].
proof.
ecall (rpg_correctness_bounds_hl p).

(*hoare A ==> B
hoare A ==> C

hoare A ==> B /\ C*)



(* RPGSpec always terminates *)
lemma rpg_ll :
  islossless RPGRef.generate_password.
proof.
proc.
islossless.
  while true i.
  - move => z.
    seq 1 : (#pre).
      auto.
      call rng_ll.
      auto.
    auto.
    smt.
    hoare.
    inline *.
    auto.
    seq 3 : (#pre).   
    auto.
    while true.
    - auto.  
    - skip.
      smt.
    smt.
    skip.
    smt.
  while true (policy.`length - size generatedPassword).
  - auto.
    inline RPGRef.random_char_generator.
    seq 1 : (#pre).
      auto.
      auto.
    seq 1 : (#pre).
      auto.
      call rng_ll.
      skip.
      smt.
    inline *.
    auto.
    smt.
    hoare.
    inline *.
    auto.
    seq 3 : (#pre).    
      auto.
    while true.
    - auto.
    - skip.
      smt.
    smt.
    hoare.
    auto.
    smt.
  - skip.
    smt.
  while true (policy.`specialMin - i).
  - auto.
    inline RPGRef.random_char_generator.
    auto.
    seq 2 : (#pre).
      auto.
      auto.    
    call rng_ll.
    auto.
    smt.
    hoare.
    auto.
    smt.
  - auto.
    smt.
  while true (policy.`numbersMin - i).
  - auto.
    inline RPGRef.random_char_generator.
    auto.
    seq 2 : (#pre).
      auto.
      auto.    
    call rng_ll.
    auto.
    smt.
    hoare.
    auto.
    smt.
  - auto.
    smt.
  while true (policy.`uppercaseMin - i).
  - auto.
    inline RPGRef.random_char_generator.
    auto.
    seq 2 : (#pre).
      auto.
      auto.    
    call rng_ll.
    auto.
    smt.
    hoare.
    auto.
    smt.
  - auto.
    smt.
  while true (policy.`lowercaseMin - i).
  - auto.
    inline RPGRef.random_char_generator.
    auto.
    seq 2 : (#pre).
      auto.
      auto.    
    call rng_ll.
    auto.
    smt.
    hoare.
    auto.
    smt.
  - auto.
    smt.
qed.






(* RPGSpec is correct *)
lemma rpg_correct &m (p:policy) :
  Pr[Correctness(RPGRef).main(p) @ &m : res] = 1%r.
proof.
byphoare.
proc.
if.
seq 1 : (#pre /\ lowercaseSet = [97; 97; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109;
         110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122]).
 auto.
 inline *.
 auto.
seq 1 : (#pre /\ uppercaseSet = [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78; 79; 80;
         81; 82; 83; 84; 85; 86; 87; 88; 89; 90]).
 auto.
 inline *.
 auto.
seq 1 : (#pre /\ numbersSet = [48; 49; 50; 51; 52; 53; 54; 55; 56; 57]).
 auto.
 inline *.
 auto.
seq 1 : (#pre /\ specialSet = [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61]).
 auto.
 inline *.
 auto.
seq 1 : (#pre /\
         size pw = policy.`length /\
         satisfiesMin policy.`lowercaseMin lowercaseSet pw /\
         satisfiesMax policy.`lowercaseMax lowercaseSet pw /\
         satisfiesMin policy.`uppercaseMin uppercaseSet pw /\
         satisfiesMax policy.`uppercaseMax uppercaseSet pw /\
         satisfiesMin policy.`numbersMin numbersSet pw /\
         satisfiesMax policy.`numbersMax numbersSet pw /\
         satisfiesMin policy.`specialMin specialSet pw /\
         satisfiesMax policy.`specialMax specialSet pw).
auto.
ecall ().
hoare.
islossless.
admit. admit. admit. admit. admit.
by conseq rpg_ll rpg_correctness_hl.
