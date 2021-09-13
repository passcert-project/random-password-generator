require import AllCore IntDiv Number Distr List PassCertRPG_jazz PassCertRPG_ref.
from Jasmin require import JModel.

op EqWordChar word char = W8.to_uint word = char.
op EqWordInt word int = W64.to_uint word = int.
op EqIntWord int word = W64.of_int int = word.


op policyFitsW64 policy =
  0 <= policy.`length < W64.modulus /\
  0 <= policy.`lowercaseMin < W64.modulus /\
  0 <= policy.`lowercaseMax < W64.modulus /\
  0 <= policy.`uppercaseMin < W64.modulus /\
  0 <= policy.`uppercaseMax < W64.modulus /\
  0 <= policy.`numbersMin < W64.modulus /\
  0 <= policy.`numbersMax < W64.modulus /\
  0 <= policy.`specialMin < W64.modulus /\
  0 <= policy.`specialMax < W64.modulus.


op policyInMem policy mem policyAddr =
  EqWordInt (loadW64 mem (W64.to_uint policyAddr)) policy.`length /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+8)) policy.`lowercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+16)) policy.`lowercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+24)) policy.`uppercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+32)) policy.`uppercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+40)) policy.`numbersMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+48)) policy.`numbersMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+56)) policy.`specialMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+64)) policy.`specialMax.


op memP_eq_specP policy (length lowercase_min lowercase_max uppercase_min uppercase_max
                 numbers_min numbers_max special_min special_max) =
  EqWordInt length policy.`length /\
  EqWordInt lowercase_min policy.`lowercaseMin /\
  EqWordInt lowercase_max policy.`lowercaseMax /\
  EqWordInt uppercase_min policy.`uppercaseMin /\
  EqWordInt uppercase_max policy.`uppercaseMax /\
  EqWordInt numbers_min policy.`numbersMin /\
  EqWordInt numbers_max policy.`numbersMax /\
  EqWordInt special_min policy.`specialMin /\
  EqWordInt special_max policy.`specialMax.


op satisfiableMemPolicy (length
                         lowercase_min lowercase_max
                         uppercase_min uppercase_max
                         numbers_min numbers_max
                         special_min special_max) =
  (length \ule (of_int 200)%W64) /\
  (W64.zero \ult length) /\
  (W64.zero \ule lowercase_min) /\
  (W64.zero \ule uppercase_min) /\
  (W64.zero \ule numbers_min) /\
  (W64.zero \ule special_min) /\
  (lowercase_max \ule (of_int 200)%W64) /\
  (uppercase_max \ule (of_int 200)%W64) /\
  (numbers_max \ule (of_int 200)%W64) /\
  (special_max \ule (of_int 200)%W64) /\
  (lowercase_min \ule lowercase_max) /\
  (uppercase_min \ule uppercase_max) /\
  (numbers_min \ule numbers_max) /\
  (special_min \ule special_max) /\
  (lowercase_min + uppercase_min + numbers_min + special_min \ule length) /\
  (length \ule lowercase_max + uppercase_max + numbers_max + special_max).

  


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

    var policyAddr, pwdAddr : W64.t;
    var output : W64.t;
    var pwd : password;
    var pwdOpt : password option;

    (* arbitrary memory location for policy and output password *)
    policyAddr <- W64.of_int 0;
    pwdAddr <- W64.of_int 1000;

    policySpecToMem(policy, Glob.mem, policyAddr);
    
    output <- M.generate_password(policyAddr, pwdAddr);

    if (output \slt W64.zero) {
      pwdOpt <- None;
    } else {
      pwd <- pwdMemToSpec(policy.`length, Glob.mem, pwdAddr);
      pwdOpt <- Some pwd;
    }

    return pwdOpt;


  }

}.


(**********************************)
(*        AUXILIARY LEMMAS        *)
(**********************************)

lemma wordint_to_intword word int :
  EqWordInt word int => EqIntWord int word.
proof.
rewrite /EqWordInt /EqIntWord.
move => h1.
by rewrite - h1.
qed.

(* lemma intword_to_wordint*)


(*lemma load_from_store mem addr word :
  loadW64 (storeW64 mem addr word) (addr) = word.
proof.
admit.
admitted.


lemma imp_policy_mem _policy _mem _policyAddr :
  hoare[ConcreteScheme.policySpecToMem : policy = _policy /\
                                         mem = _mem /\
                                         addr = _policyAddr /\
                                         policyFitsW64 _policy
         ==> 
        policyInMem _policy _mem _policyAddr].
proof.
proc.
(*facil meter mais pequena... mas n sei mudar mem para _mem*)
seq 1 : (policy = _policy /\
         policyFitsW64 _policy /\
         EqWordInt (loadW64 mem (to_uint addr)) policy.`length).
- wp.
  skip.
  move => &m /> ????????????.
  rewrite /EqWordInt.
  rewrite load_from_store to_uint_small.
  by do! split.
  move => />.   
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+8)) policy.`lowercaseMin).
- wp.
  skip.
  move => &m /> ???????????????????.
  rewrite /EqWordInt.
  rewrite load_from_store to_uint_small.
  smt(@Int). (* nao percebo bem se isto faz sentido *)
admit.  
admit.  
admitted.*)


lemma sat_mem_sat_spec policy length lowercase_min lowercase_max uppercase_min
                       uppercase_max numbers_min numbers_max special_min special_max :
  (memP_eq_specP policy length lowercase_min lowercase_max uppercase_min
                 uppercase_max numbers_min numbers_max special_min special_max) =>
  (satisfiableMemPolicy length
                        lowercase_min lowercase_max
                        uppercase_min uppercase_max
                        numbers_min numbers_max
                        special_min special_max)
    <=>
  (satisfiablePolicy policy).
proof.
move => /> ?????????.
split.
* move => /> ????????????????. 
  do! split.
  - rewrite uleE in H8. rewrite of_uintK in H8. rewrite -H. smt. (*ez fix*)
  - rewrite ultE in H9. rewrite of_uintK in H9. by rewrite -H.
  - rewrite uleE in H10. rewrite of_uintK in H10. by rewrite -H0.
  - rewrite uleE in H11. rewrite of_uintK in H11. by rewrite -H2.
  - rewrite uleE in H12. rewrite of_uintK in H12. by rewrite -H4.
  - rewrite uleE in H13. rewrite of_uintK in H13. by rewrite -H6.
  - rewrite uleE in H14. rewrite of_uintK in H14. rewrite -H1. smt.
  - rewrite uleE in H15. rewrite of_uintK in H15. rewrite -H3. smt.
  - rewrite uleE in H16. rewrite of_uintK in H16. rewrite -H5. smt.
  - rewrite uleE in H17. rewrite of_uintK in H17. rewrite -H7. smt.
  - rewrite uleE in H18. by rewrite -H0 -H1.
  - rewrite uleE in H19. by rewrite -H2 -H3.
  - rewrite uleE in H20. by rewrite -H4 -H5.
  - rewrite uleE in H21. by rewrite -H6 -H7.
  - rewrite uleE in H22. rewrite -H0 -H2 -H4 -H6 -H.
    rewrite -to_uintD_small. smt. (*Fix*)
    rewrite -to_uintD_small. smt.
    rewrite -to_uintD_small. smt.
    assumption.
  - rewrite uleE in H23. rewrite -H1 -H3 -H5 -H7 -H.
    rewrite -to_uintD_small. smt.
    rewrite -to_uintD_small. smt.
    rewrite -to_uintD_small. smt.
    assumption.
* move => /> ????????????????.
  do! split.
  - rewrite uleE. rewrite of_uintK. rewrite -H in H8. smt.
  - rewrite ultE. rewrite of_uintK. by rewrite -H in H9.
  - rewrite uleE. rewrite of_uintK. by rewrite -H0 in H10.
  - rewrite uleE. rewrite of_uintK. by rewrite -H2 in H11.
  - rewrite uleE. rewrite of_uintK. by rewrite -H4 in H12.
  - rewrite uleE. rewrite of_uintK. by rewrite -H6 in H13.
  - rewrite uleE. rewrite of_uintK. rewrite -H1 in H14. smt.
  - rewrite uleE. rewrite of_uintK. rewrite -H3 in H15. smt.
  - rewrite uleE. rewrite of_uintK. rewrite -H5 in H16. smt.
  - rewrite uleE. rewrite of_uintK. rewrite -H7 in H17. smt.
  - rewrite uleE. by rewrite -H0 -H1 in H18.
  - rewrite uleE. by rewrite -H2 -H3 in H19.
  - rewrite uleE. by rewrite -H4 -H5 in H20.
  - rewrite uleE. by rewrite -H6 -H7 in H21.
  - rewrite uleE. rewrite -H0 -H2 -H4 -H6 -H in H22.
    rewrite to_uintD_small. smt. (*Fix*)
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    assumption.
  - rewrite uleE. rewrite -H1 -H3 -H5 -H7 -H in H23.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    assumption.

qed.


(*********************************)
(*          EQUIVALENCE          *)
(*********************************)

lemma imp_ref_rng_equiv :
  equiv[M.rng ~ RPGRef.rng : EqWordInt range{1} range{2} /\
                             to_uint range{1} < W64.modulus /\
                             0 < to_uint range{1}
                             ==> EqWordInt res{1} res{2}].
proof.
proc.
seq 5 1 : (#pre /\
           EqWordInt tmp1{1} modValue{2} /\
           EqWordInt tmp_range{1} (range{2} - 1) /\
           EqWordInt tmp2{1} (2^64-1)).
- wp.
  skip.
  move => &1 &2 [h1 [h2 h3]] />.
  rewrite umodE /ulift2 h1 /= /EqWordInt.
  rewrite to_uint_small.
  split.
  + by apply modn_ge0.
  + move => h4.
    rewrite -h1.
    have mod : 18446744073709551615 %% to_uint range{1} < to_uint range{1}.
    * by apply ltz_pmod.
    smt. (* fixme ltr_trans not working *)
  do! split.
  rewrite - h1.
  have mod64 : W64.modulus = 18446744073709551616.
  - smt.
  by rewrite - mod64.
  rewrite to_uintB.
  rewrite ltzE in h3.
  by rewrite uleE /=.
  by rewrite - h1 /=.
  by rewrite to_uint_small.
if.
- move => &1 &2 [h1 [h2 [h3 h4]]] />.
  split.
  + move => h5.
    rewrite -h2 -h3.
    congr.
  + move => h5. 
    smt. (*fix*)
- seq 1 1 : (#[/:]pre /\ EqWordInt max_value{1} maxValue{2}).
  + wp.
    by skip.
  seq 1 1 : (#[/:]pre /\ EqWordInt tmp2{1} value{2}).
  + admit.
admitted.



lemma implementation_reference_equiv :
  equiv[ConcreteScheme.generate_password ~ RPGRef.generate_password :
          ={policy} /\ policyFitsW64 policy{1} ==> ={res}].
proof.
proc.
seq 3 0 : (#pre /\
           policyAddr{1} = W64.zero /\
           policyInMem policy{1} Glob.mem{1} (W64.zero)).
seq 2 0 : (#pre /\ policyAddr{1} = W64.zero).
- auto.
(*ecall{1} (imp_policy_mem policy{1} Glob.mem{1} policyAddr{1}).*)
admit.
inline M.generate_password.
seq 17 0 : (={policy} /\
            memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
            tmp64_1{1} = length{1}).
- auto.
  move => &m1 &m2 />.
if{1}.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1}).
by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64 /\
           lowercase_min{1} \ule lowercase_max{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64 /\
           lowercase_min{1} \ule lowercase_max{1} /\
           uppercase_min{1} \ule uppercase_max{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64 /\
           lowercase_min{1} \ule lowercase_max{1} /\
           uppercase_min{1} \ule uppercase_max{1} /\
           numbers_min{1} \ule numbers_max{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64 /\
           lowercase_min{1} \ule lowercase_max{1} /\
           uppercase_min{1} \ule uppercase_max{1} /\
           numbers_min{1} \ule numbers_max{1} /\
           special_min{1} \ule special_max{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1} /\
           W64.zero \ule uppercase_min{1} /\
           W64.zero \ule numbers_min{1} /\
           W64.zero \ule special_min{1} /\
           lowercase_max{1} \ule (of_int 200)%W64 /\
           uppercase_max{1} \ule (of_int 200)%W64 /\
           numbers_max{1} \ule (of_int 200)%W64 /\
           special_max{1} \ule (of_int 200)%W64 /\
           lowercase_min{1} \ule lowercase_max{1} /\
           uppercase_min{1} \ule uppercase_max{1} /\
           numbers_min{1} \ule numbers_max{1} /\
           special_min{1} \ule special_max{1} /\
           lowercase_min{1} + uppercase_min{1} + numbers_min{1} + special_min{1} \ule length{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           memP_eq_specP policy{1} length{1} lowercase_min{1} lowercase_max{1}
                         uppercase_min{1} uppercase_max{1} numbers_min{1}
                         numbers_max{1} special_min{1} special_max{1} /\
           satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
                                uppercase_min{1} uppercase_max{1}
                                numbers_min{1} numbers_max{1}
                                special_min{1} special_max{1}).
- by skip.
if{2}.
(* if both mem and spec are satisfiable... distribution on the output should be equal *)
(* talvez seja necessario tirar informacoes sobre equivalencia entre os conjuntos *)
seq 0 4 : (#pre).
- inline *.
  auto.
seq 26 0 : (#pre).
- auto.
sp.

admit.

(* if spec policy is unsat and mem policy is sat *)
conseq (_: false ==> _).
move => &m1 &m2 [[h1 [h2 h3]] h4].
have sat : satisfiablePolicy policy{m1}.
- by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
subst policy{m1}.
trivial.
trivial.

(* if mem length > maxsum *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_2{m1} tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem length < minsum *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_2{m1} tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem special min > special max *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1} tmp64_2{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.


(* if mem numbers min > numbers max *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1} tmp64_2{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem uppercase min > uppercase max *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1} tmp64_2{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem lowercase min > lowercase max *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1} tmp64_2{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem special max > 200 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem numbers max > 200 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem uppercase max > 200 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem lowercase max > 200 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem special min < 0 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem numbers min < 0 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem uppercase min < 0 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem lowercase min < 0 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 h5]]]] h6] h7].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem length < 0 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[[h1 [h2 h3]] h4] h5] h6].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.

(* if mem length > 200 *)
if{2}.
* conseq (_: false ==> _).
  move => &m1 &m2 [[[h1 [h2 h3]] h4] h5].
  subst policy{m2}.
  have sat : satisfiableMemPolicy length{m1}
                                  lowercase_min{m1} lowercase_max{m1}
                                  uppercase_min{m1} uppercase_max{m1}
                                  numbers_min{m1} numbers_max{m1}
                                  special_min{m1} special_max{m1}.
  - by apply (sat_mem_sat_spec policy{m1} length{m1}
                          lowercase_min{m1} lowercase_max{m1}
                          uppercase_min{m1} uppercase_max{m1}
                          numbers_min{m1} numbers_max{m1}
                          special_min{m1} special_max{m1}).
  subst tmp64_1{m1}.
  smt.
  trivial.
* sp.
  if{1}.
  - auto.
  - conseq (_: false ==> _).
    move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
    subst output{m1} output0{m1}.
    rewrite sltE !of_sintK /smod /= in h5.
    trivial.
    trivial.
admitted.


(*********************************)
(*          CORRECTNESS          *)
(*********************************)

lemma concrete_rpg_correctness &m policy :
  Pr[Correctness(ConcreteScheme).main(policy) @ &m : res] = 1%r.
proof.






(*********************************)
(*           SECURITY            *)
(*********************************)
