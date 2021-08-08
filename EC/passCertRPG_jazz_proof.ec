require import AllCore Distr List PassCertRPG_jazz.
from Jasmin require import JModel.
require RPGTh.

clone include RPGTh.

(*abbrev EqWordInt word num = W64.to_uint word = num.*)

module ConcreteScheme : RPG_T = {

  proc policySpecToMem(policy:policy, mem:global_mem_t, addr:W64.t) = {
    mem <- storeW64 mem (W64.to_uint addr + 0) (W64.of_int policy.`length);
    mem <- storeW64 mem (W64.to_uint addr + 8) (W64.of_int policy.`lowercaseMin);
    mem <- storeW64 mem (W64.to_uint addr + 16) (W64.of_int policy.`lowercaseMax);
    mem <- storeW64 mem (W64.to_uint addr + 24) (W64.of_int policy.`uppercaseMin);
    mem <- storeW64 mem (W64.to_uint addr + 32) (W64.of_int policy.`uppercaseMax);
    mem <- storeW64 mem (W64.to_uint addr + 40) (W64.of_int policy.`numbersMin);
    mem <- storeW64 mem (W64.to_uint addr + 48) (W64.of_int policy.`numbersMax);
    mem <- storeW64 mem (W64.to_uint addr + 56) (W64.of_int policy.`specialMin);
    mem <- storeW64 mem (W64.to_uint addr + 64) (W64.of_int policy.`specialMax);
  }

  proc pwdMemToSpec(length:int, mem:global_mem_t, addr:W64.t) : password = {
    var pwd;
    var i;

    pwd <- [];
    i <- 0;
    while(i < length) {
      pwd <- pwd ++ [W8.to_uint (loadW8 mem (W64.to_uint addr + i))];
    }

    return pwd;
  }


  proc generate_password(policy:policy) : password option = {

    var mem : global_mem_t;
    var policyAddr, pwdAddr : W64.t;
    var output : W64.t;
    var pwd : password;
    var pwdOpt : password option;

    (* arbitrary memory location for policy and output password *)
    policyAddr <- W64.of_int 0;
    pwdAddr <- W64.of_int 1000;

    policySpecToMem(policy, mem, policyAddr);
    
    output <- M.generate_password(policyAddr, pwdAddr);

    if (W64.to_uint output < 0) {
      pwdOpt <- None;
    } else {
      pwd <- pwdMemToSpec(policy.`length, mem, pwdAddr);
      pwdOpt <- Some pwd;
    }

    return pwdOpt;


  }

}.


lemma implementation_reference_equiv &m policy :
  equiv





(*********************************)
(*          CORRECTNESS          *)
(*********************************)

lemma concrete_rpg_correctness &m policy :
  Pr[Correctness(ConcreteScheme).main(policy) @ &m : res] = 1%r.
proof.











(*********************************)
(*           SECURITY            *)
(*********************************)
