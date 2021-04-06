require import AllCore List.

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
