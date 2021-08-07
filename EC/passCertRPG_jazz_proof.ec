require import AllCore Distr List PassCertGenerator_jazz.
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
  generate_password
}.

lemma concrete_rpg_correctness &m (length:W64.t, lowercase_policies:W64.t,
                                   uppercase_policies:W64.t, numbers_policies:W64.t,
                                   special_policies:W64.t, p_output:W64.t) :
  Pr[Correctness(ConcreteScheme).main(wordsToPolicy m length lowercase_policies uppercase_policies
                              numbers_policies special_policies) @ &m : res] = 1%r.
proof.
