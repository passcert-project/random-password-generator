require import AllCore IntDiv DInterval List UpdateList CharacterSets.

module RPGSpec = {

  proc rng(range:int) : int = {
    
    var rand_number:int;
    
    rand_number <$ [0 .. (2^64) - 1];
    rand_number <- (rand_number %% range);
    
    return rand_number;
    
  }

  
  proc random_char_generator(set:int list) : int = {
    
    var char:int;
    var choice:int;
    
    choice <@ rng(size set);
    char <- nth 0 set choice;
    
    return (char);
    
  }

  
  proc permutation(string:int list) : int list = {

    var i:int;
    var j:int;
    var aux:int;
    
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


  
  proc define_union_set(lowercase_max, uppercase_max, numbers_max, special_max) : int list = {

    var unionSet : int list;

    unionSet <- [];
    
    if (0 < lowercase_max) {
      unionSet <- unionSet ++ CharacterSets.lowercaseLetters;
    }
    if (0 < uppercase_max) {
      unionSet <- unionSet ++ CharacterSets.uppercaseLetters;
    }
    if (0 < numbers_max) {
      unionSet <- unionSet ++ CharacterSets.numbers;
    }
    if (0 < special_max) {
      unionSet <- unionSet ++ CharacterSets.specialCharacters;
    }

    return unionSet;    

  }



  
  
  proc generate_password(length:int, lowercase_min:int, lowercase_max:int,
  uppercase_min:int, uppercase_max:int, numbers_min:int, numbers_max:int,
  special_min:int, special_max:int) : int list = {

    var password, unionSet : int list;
    var i, randomChar : int;
    
    (* length is smaller than 200*)
    if (length <= 200) {
    (* length is greater than 0*)
    if (0 <= length) {
    (* min values are not negative*)
    if (0 <= lowercase_min) {
    if (0 <= uppercase_min) {
    if (0 <= numbers_min) {
    if (0 <= special_min) {
    (* max values are not negative *)
    if (0 <= lowercase_max) {
    if (0 <= uppercase_max) {
    if (0 <= numbers_max) {
    if (0 <= special_max) {
    (* max values are larger or equal to min values *)
    if (lowercase_min <= lowercase_max) {
    if (uppercase_min <= uppercase_max) {
    if (numbers_min <= numbers_max) {
    if (special_min <= special_max) {
    (* sum of min values does not exceed length *)
    if (lowercase_min + uppercase_min + numbers_min + special_min <= length) {
    (* sum of max values satisfies length *)
    if (length <= lowercase_max + uppercase_max + numbers_max+ special_max) {

      (* READY TO GENERATE PASSWORD *)

      CharacterSets.init();
      password <- [];

      (* Generate characters with min values defined*)
      
      if (0 < lowercase_max) {
        i <- 0;
        while (i < lowercase_min) {
          lowercase_max <- lowercase_max - 1;
          randomChar <@ random_char_generator(CharacterSets.lowercaseLetters);
          password <- password ++ [randomChar];
          i <- i + 1;
        }
      }
      if (0 < uppercase_max) {
        i <- 0;
        while (i < uppercase_min) {
          uppercase_max <- uppercase_max - 1;
          randomChar <@ random_char_generator(CharacterSets.uppercaseLetters);
          password <- password ++ [randomChar];
          i <- i + 1;
        }
      }
      if (0 < numbers_max) {
        i <- 0;
        while (i < numbers_min) {
          numbers_max <- numbers_max - 1;
          randomChar <@ random_char_generator(CharacterSets.numbers);
          password <- password ++ [randomChar];
          i <- i + 1;
        }
      }
      if (0 < special_max) {
        i <- 0;
        while (i < special_min) {
          special_max <- special_max - 1;
          randomChar <@ random_char_generator(CharacterSets.specialCharacters);
          password <- password ++ [randomChar];
          i <- i + 1;
        }
      }

      (* Generate characters from the available sets of characters *)
      unionSet <@ define_union_set(lowercase_max, uppercase_max, numbers_max, special_max);

      while (size password < length) {

        randomChar <@ random_char_generator(unionSet);

        if (mem CharacterSets.lowercaseLetters randomChar) {
          lowercase_max <- lowercase_max - 1;
          if (lowercase_max = 0) {
            unionSet <@ define_union_set(lowercase_max, uppercase_max, numbers_max, special_max);
          }
        }
        elif (mem CharacterSets.uppercaseLetters randomChar) {
          uppercase_max <- uppercase_max - 1;
          if (uppercase_max = 0) {
            unionSet <@ define_union_set(lowercase_max, uppercase_max, numbers_max, special_max);
          }
        }
        elif (mem CharacterSets.numbers randomChar) {
          numbers_max <- numbers_max - 1;
          if (numbers_max = 0) {
            unionSet <@ define_union_set(lowercase_max, uppercase_max, numbers_max, special_max);
          }
        }
        elif (mem CharacterSets.specialCharacters randomChar) {
          special_max <- special_max - 1;
          if (special_max = 0) {
            unionSet <@ define_union_set(lowercase_max, uppercase_max, numbers_max, special_max);
          }
        }

      }

      password <@ permutation(password);

                                 
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }    
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    } 
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }
    } else {
      password <- [];
    }

    return password;
    

  }
  
}.

