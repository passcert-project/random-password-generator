require import AllCore Distr List PassCertRPG_jazz.
from Jasmin require import JModel.
require RPGTh.

clone include RPGTh.

abbrev EqWordInt word num = W64.to_uint word = num.

op wordsToPolicy m lengthP lowercaseP uppercaseP numbersP specialP : policy =
  {|length=lengthP;
    lowercaseMin=W64.to_uint (loadW64 m (W64.to_uint lowercaseP));
    lowercaseMax=W64.to_uint (loadW64 m (W64.to_uint (lowercaseP + W64.of_int 8)));
    uppercaseMin=W64.to_uint (loadW64 m (W64.to_uint uppercaseP));
    uppercaseMax=W64.to_uint (loadW64 m (W64.to_uint (uppercaseP + W64.of_int 8)));
    numbersMin=W64.to_uint (loadW64 m (W64.to_uint numbersP));
    numbersMax=W64.to_uint (loadW64 m (W64.to_uint (numbersP + W64.of_int 8)));
    specialMin=W64.to_uint (loadW64 m (W64.to_uint specialP));
    specialMax=W64.to_uint (loadW64 m (W64.to_uint (specialP + W64.of_int 8)));|}.



module ConcreteScheme : RPG_T = {

  var globalMem : global_mem_t
  var lowercaseAddr, uppercaseAddr, numbersAddr, specialAddr, outputAddr : W64.t

  proc policyToMem(policy:policy) = {
    globalMem <- storeW64 globalMem (W64.to_uint lowercaseAddr) (W64.of_int policy.`lowercaseMin);
    globalMem <- storeW64 globalMem (W64.to_uint (lowercaseAddr + (W64.of_int 8)))
                 (W64.of_int policy.`lowercaseMax);
    globalMem <- storeW64 globalMem (W64.to_uint uppercaseAddr) (W64.of_int policy.`uppercaseMin);
    globalMem <- storeW64 globalMem (W64.to_uint (uppercaseAddr + (W64.of_int 8)))
                 (W64.of_int policy.`uppercaseMax);
    globalMem <- storeW64 globalMem (W64.to_uint numbersAddr) (W64.of_int policy.`numbersMin);
    globalMem <- storeW64 globalMem (W64.to_uint (numbersAddr + (W64.of_int 8)))
                 (W64.of_int policy.`numbersMax);
    globalMem <- storeW64 globalMem (W64.to_uint specialAddr) (W64.of_int policy.`specialMin);
    globalMem <- storeW64 globalMem (W64.to_uint (specialAddr + (W64.of_int 8)))
                 (W64.of_int policy.`specialMax);
  }

  proc generate_password(policy:policy) : password option = {

    var feedback : W64.t;
    var output : password option;

    lowercaseAddr <- W64.of_int 0;
    uppercaseAddr <- W64.of_int 200;
    numbersAddr <- W64.of_int 400;
    specialAddr <- W64.of_int 600;
    outputAddr <- W64.of_int 800;

    policyToMem(policy);
    
    feedback <- M.generate_password(W64.of_int policy.`length, lowercaseAddr, uppercaseAddr,
                                  numbersAddr, specialAddr, outputAddr);

    if (W64.to_uint feedback < 0) {
      output <- None;
    } else {
      
    }

    return output;


  }

}.


lemma concrete_rpg_correctness &m policy :
  Pr[Correctness(ConcreteScheme).main(policy) @ &m : res] = 1%r.
proof.
