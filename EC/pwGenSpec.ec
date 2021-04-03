require import AllCore IntDiv DInterval List.

module RPGSpec = {

  
  proc rng(range:int) : int = {
    
    var rand_number:int;
    
    rand_number <$ [0 .. (2^64)-1];
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
      string <- insert (nth 0 string j) string i;
      string <- insert aux string j;
    }
    
    return string;
    
  }

  
  proc generatePassword(length:int, lowercase_min:int, lowercase_max:int,
  uppercase_min:int, uppercase_max:int, numbers_min:int, numbers_max:int,
  special_min:int, special_max:int) : int list = {


    return [];
    

  }
  
}.

