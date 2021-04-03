(* EC Theory of Random Password Generators *)

require import AllCore List.
require import PwGenSpec.

require import Array76.
require import WArray76.

(* Character Sets *)
module CharacterSets = {

  var lowercaseLetters : int list
  var uppercaseLetters : int list
  var numbers : int list
  var specialCharacters : int list

  proc init() = {
    lowercaseLetters <- 97::97::99::100::101::102::103::104::105::106::107::108::109::110::111::
                        112::113::114::115::116::117::118::119::120::121::122::[];
    uppercaseLetters <- 65::66::67::68::69::70::71::72::73::74::75::76::77::78::79::80::81::82::
                        83::84::85::86::87::88::89::90::[];
    numbers <- 48::49::50::51::52::53::54::55::56::57::58::[];
    specialCharacters <- 33::63::35::36::37::38::43::45::42::95::64::58::59::61::[];
  }
  
}.

(* If, given a concrete password generator, the main procedure of the following module
    is true with 100% probability, then it means that the password generator always terminates *)

module Termination = {
  
  proc main(length:int, lowercase_min:int, lowercase_max:int, uppercase_min:int,
  uppercase_max:int, numbers_min:int, numbers_max:int, special_min:int, special_max:int)
  : bool = {
    
  RPGSpec.generatePassword(length, lowercase_min, lowercase_max, uppercase_min,
  uppercase_max, numbers_min, numbers_max, special_min, special_max);
    
    return true;
    
  }
  
}.


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
    
    var generatedPassword : int list;
    var output : bool;
    
    generatedPassword <@ RPGSpec.generatePassword(length, lowercase_min, lowercase_max,
    uppercase_min, uppercase_max, numbers_min, numbers_max, special_min, special_max);

    output <@ satisfiesPolicies(length, lowercase_min, lowercase_max, uppercase_min,
    uppercase_max, numbers_min, numbers_max, special_min, special_max, generatedPassword);

    return output;
    
  }

}.
