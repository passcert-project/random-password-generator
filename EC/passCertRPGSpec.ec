require import AllCore IntDiv DInterval List UpdateList.
require (****) RPG.

clone include RPG.

module RPGSpec : RPG_T = {

  proc rng(range:int) : int = {
    
    var rand_number:int;
    
    rand_number <$ [0 .. (2^64) - 1];
    rand_number <- (rand_number %% range);
    
    return rand_number;
    
  }

  
  proc random_char_generator(set:charSet) : char = {
    
    var char:char;
    var choice:int;
    
    choice <@ rng(size set);
    char <- nth (-1) set choice;
    
    return (char);
    
  }

  
  proc permutation(string:int list) : int list = {

    var i:int;
    var j:int;
    var aux:char;
    
    i <- size string;
    
    while (0 < i) {
      j <@ rng(i);
      i <- i - 1;
      aux <- nth 0 string i;
      string <- update (nth 0 string j) string i;
      string <- update aux string j;
    }
    
    return string;
    
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
    set <- [48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 58];
    return set;

  }


  proc get_special() : charSet = {
    
    var set : charSet;
    set <- [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61];
    return set;

  }


  proc define_union_set(lowercase_max, uppercase_max, numbers_max, special_max) : charSet = {

    var unionSet, set : charSet;

    unionSet <- [];
    
    if (0 < lowercase_max) {
      set <- get_lowercase();
      unionSet <- unionSet ++ set;
    }
    if (0 < uppercase_max) {
      set <- get_uppercase();
      unionSet <- unionSet ++ set;
    }
    if (0 < numbers_max) {
      set <- get_numbers();
      unionSet <- unionSet ++ set;
    }
    if (0 < special_max) {
      set <- get_special();
      unionSet <- unionSet ++ set;
    }

    return unionSet;    

  }

  
  proc generate_password(policy:policy) : password = {

    var generatedPassword: password;
    var unionSet, lowercaseSet, uppercaseSet, numbersSet, specialSet : charSet;
    var randomChar : char;
    var i : int;
    var lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable : int;

    generatedPassword <- [];

    (* initializer sets *)
    lowercaseSet <@ get_lowercase();
    uppercaseSet <@ get_uppercase();
    numbersSet <@ get_numbers();
    specialSet <@ get_special();
    
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
                                 specialAvailable);

     while (size generatedPassword < policy.`length) {

        randomChar <@ random_char_generator(unionSet);

        if (mem lowercaseSet randomChar) {
          lowercaseAvailable <- lowercaseAvailable - 1;
          if (lowercaseAvailable = 0) {
            unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable);
          }
        }
        elif (mem uppercaseSet randomChar) {
          uppercaseAvailable <- uppercaseAvailable - 1;
          if (uppercaseAvailable = 0) {
            unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable);
          }
        }
        elif (mem numbersSet randomChar) {
          numbersAvailable <- numbersAvailable - 1;
          if (numbersAvailable = 0) {
            unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable);
          }
        }
        elif (mem specialSet randomChar) {
          specialAvailable <- specialAvailable - 1;
          if (specialAvailable = 0) {
            unionSet <@ define_union_set(lowercaseAvailable, uppercaseAvailable, numbersAvailable, specialAvailable);
          }
        }

      }

      generatedPassword <@ permutation(generatedPassword);

    return generatedPassword;
    

  }
  
}.


(**********************************)
(*        AUXILIARY LEMMAS        *)
(**********************************)

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


(*********************************)
(*          CORRECTNESS          *)
(*********************************)


