require import AllCore Number IntDiv Distr DInterval List PassCertRPG_jazz PassCertRPG_ref.
from Jasmin require import JModel.

(*-------------------------------*)
(*----- Auxiliary operators -----*)
(*-------------------------------*)

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

op policyInMem mem policyAddr policy =
  EqWordInt (loadW64 mem (W64.to_uint policyAddr)) policy.`length /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+8)) policy.`lowercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+16)) policy.`lowercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+24)) policy.`uppercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+32)) policy.`uppercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+40)) policy.`numbersMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+48)) policy.`numbersMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+56)) policy.`specialMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+64)) policy.`specialMax.

op memPolicy_eq_specPolicy policy (length lowercase_min lowercase_max uppercase_min uppercase_max
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


op memPassword_eq_specPassword_length mem passwordAddr length password =
  forall n, n \in range 0 length =>
  nth (-1) password n = W8.to_uint (loadW8 mem (W64.to_uint passwordAddr + n)).

op memPassword_eq_specPassword mem passwordAddr password =
  memPassword_eq_specPassword_length mem passwordAddr (size password) password.


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


(*op memSet_eq_specSet memSet specSet =
  forall x, (x \in memSet /\ !(x = W8.zero)) => exists y, y \in specSetEqWordChar*)

module ConcreteScheme : RPG_T = {

  proc policySpecToMem(policy:policy, mem:global_mem_t, addr:W64.t) : global_mem_t = {
    mem <- storeW64 mem (W64.to_uint addr + 0) (W64.of_int policy.`length);
    mem <- storeW64 mem (W64.to_uint addr + 8) (W64.of_int policy.`lowercaseMin);
    mem <- storeW64 mem (W64.to_uint addr + 16) (W64.of_int policy.`lowercaseMax);
    mem <- storeW64 mem (W64.to_uint addr + 24) (W64.of_int policy.`uppercaseMin);
    mem <- storeW64 mem (W64.to_uint addr + 32) (W64.of_int policy.`uppercaseMax);
    mem <- storeW64 mem (W64.to_uint addr + 40) (W64.of_int policy.`numbersMin);
    mem <- storeW64 mem (W64.to_uint addr + 48) (W64.of_int policy.`numbersMax);
    mem <- storeW64 mem (W64.to_uint addr + 56) (W64.of_int policy.`specialMin);
    mem <- storeW64 mem (W64.to_uint addr + 64) (W64.of_int policy.`specialMax);

    return mem;
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

lemma RDRAND_dinterval:
 RDRAND2 = dmap [0..W64.max_uint] W64.of_int.
proof.
rewrite /RDRAND2 /dword.
apply eq_distr => x.
rewrite duniform1E dmap1E all_wordsP /= /all_words.
rewrite undup_id.
 rewrite map_inj_in_uniq.
  move=> a b Ha Hb H.
 have: W64.to_uint (W64.of_int a) = W64.to_uint (W64.of_int b) by smt().
  rewrite !of_uintK !modz_small; smt.
 by apply iota_uniq.
rewrite size_map size_iota dinterE /=.
have ->: size (filter (pred1 x \o W64.of_int) (range 0 18446744073709551616)) = 1.
 rewrite size_filter (eq_in_count _ (pred1 (W64.to_uint x))).
  move => a /mem_range [? ?].
  rewrite /(\o) /pred1; split => H.
   by rewrite -H of_uintK modz_small /#.
  by rewrite H to_uintK.
 rewrite count_uniq_mem.
  by apply range_uniq.
 rewrite mem_range; move: (W64.to_uint_cmp x); smt().
done.
qed.

lemma wordint_to_intword word int :
  EqWordInt word int => EqIntWord int word.
proof.
rewrite /EqWordInt /EqIntWord.
move => h1.
by rewrite - h1.
qed.


lemma eqwordint_int_id x :
  0 <= x < W64.modulus =>
  EqWordInt (of_int%W64 x) x.
proof.
move => h1.
rewrite /EqWordInt to_uint_small.
assumption.
reflexivity.
qed.

lemma load_from_store mem addr word :
  loadW64 (storeW64 mem addr word) (addr) = word.
proof.
rewrite /loadW64 /storeW64 -(W8u8.unpack8K word); congr.
apply W8u8.Pack.all_eq_eq; rewrite /all_eq !storesE /=.
rewrite !get_setE => |>. smt().
qed.

lemma load_storeW64_neq mem a1 a2 x:
 (a2 + 8 <= a1 || a1 + 8 <= a2) => 
 loadW64 (storeW64 mem a1 x) a2 = loadW64 mem a2.
proof.
move => H; rewrite /loadW64 /storeW64; congr.
apply W8u8.Pack.all_eq_eq; rewrite /all_eq !storesE /=.
rewrite !get_setE => |>. smt(). 
qed.

lemma load_from_unaffected_store mem addr (pos1 pos2:int) wordX wordY :
  loadW64 mem (addr + pos1) = wordX =>
  8 <= pos2 - pos1 =>
  loadW64 (storeW64 mem (addr + pos2) wordY) (addr + pos1) = wordX. 
proof.
move=> <- *.
apply load_storeW64_neq.
smt().
qed.


lemma sat_mem_sat_spec policy length lowercase_min lowercase_max uppercase_min
                       uppercase_max numbers_min numbers_max special_min special_max :
  (memPolicy_eq_specPolicy policy length lowercase_min lowercase_max uppercase_min
                 uppercase_max numbers_min numbers_max special_min special_max) =>
  (satisfiableMemPolicy length
                        lowercase_min lowercase_max
                        uppercase_min uppercase_max
                        numbers_min numbers_max
                        special_min special_max)
    <=>
  (satisfiablePolicy policy).
proof.
move => /> h1 h2 h3 h4 h5 h6 h7 h8 h9.
split.
* move => /> h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25.
  rewrite uleE /= in h10.
  rewrite ultE /= in h11.
  rewrite uleE /= in h12.
  rewrite uleE /= in h13.
  rewrite uleE /= in h14.
  rewrite uleE /= in h15.
  rewrite uleE /= in h16.
  rewrite uleE /= in h17.
  rewrite uleE /= in h18.
  rewrite uleE /= in h19.
  rewrite uleE /= in h20.
  rewrite uleE /= in h21.
  rewrite uleE /= in h22.
  rewrite uleE /= in h23.
  rewrite uleE /= in h24.
  rewrite uleE /= in h25.
  do! split.
  - by rewrite -h1.
  - by rewrite -h1.
  - by rewrite -h2.
  - by rewrite -h4.
  - by rewrite -h6.
  - by rewrite -h8.
  - by rewrite -h3.
  - by rewrite -h5.
  - by rewrite -h7.
  - by rewrite -h9.
  - by rewrite -h2 -h3.
  - by rewrite -h4 -h5.
  - by rewrite -h6 -h7.
  - by rewrite -h8 -h9.
  - rewrite -h2 -h4 -h6 -h8 -h1.
    rewrite -to_uintD_small. smt().
    rewrite -to_uintD_small. smt.
    rewrite -to_uintD_small. smt.
    assumption.
  - rewrite -h3 -h5 -h7 -h9 -h1.
    rewrite -to_uintD_small. smt().
    rewrite -to_uintD_small. smt.
    rewrite -to_uintD_small. smt.
    assumption.
* move => /> h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25.
  do! split.
  - rewrite uleE. by rewrite -h1 in h10.
  - rewrite ultE. by rewrite -h1 in h11.
  - rewrite uleE. by rewrite -h2 in h12.
  - rewrite uleE. by rewrite -h4 in h13.
  - rewrite uleE. by rewrite -h6 in h14.
  - rewrite uleE. by rewrite -h8 in h15.
  - rewrite uleE. by rewrite -h3 in h16. 
  - rewrite uleE. by rewrite -h5 in h17.
  - rewrite uleE. by rewrite -h7 in h18.
  - rewrite uleE. by rewrite -h9 in h19.
  - rewrite uleE. by rewrite -h2 -h3 in h20.
  - rewrite uleE. by rewrite -h4 -h5 in h21.
  - rewrite uleE. by rewrite -h6 -h7 in h22.
  - rewrite uleE. by rewrite -h8 -h9 in h23.
  - rewrite uleE. rewrite -h2 -h4 -h6 -h8 -h1 in h24.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    assumption.
  - rewrite uleE. rewrite -h3 -h5 -h7 -h9 -h1 in h25.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    rewrite to_uintD_small. smt.
    assumption.
qed.


(*********************************)
(*          EQUIVALENCE          *)
(*********************************)

axiom rdrand_eq_dist :
  RDRAND = dmap [0..W64.max_uint] W64.of_int.  

lemma imp_ref_rng_equiv :
  equiv[M.rng ~ RPGRef.rng : EqWordInt range{1} range{2} /\
                             0 < to_uint range{1} < W64.modulus
                             ==> EqWordInt res{1} res{2}].
proof.
proc.
seq 5 1 : (#pre /\
           EqWordInt tmp1{1} modValue{2} /\
           EqWordInt tmp_range{1} (range{2} - 1) /\
           EqWordInt tmp2{1} (2^64-1) /\
           W64.one \ule (tmp2{1} - tmp1{1}) /\
           tmp1{1} \ule tmp2{1}).
- wp.
  skip.
  move => &1 &2 [h1 [h2 h3]] />.
  rewrite umodE /ulift2 h1 /= /EqWordInt to_uint_small.
  split.
  + by apply modn_ge0.
  + move => h4.
    rewrite -h1.
    have mod : 18446744073709551615 %% to_uint range{1} < to_uint range{1}.
    * by apply ltz_pmod.
    (*apply (ltr_trans mod h3). cant find the lemma for some reason*)
    smt.
  do! split.
  + rewrite to_uintB.
    rewrite uleE /=.
    smt().
    by rewrite h1 /=.
  + rewrite uleE /=.
    smt.
  + smt.
if.
- move => &1 &2 [h1 [h2 [h3 h4]]] />.
  split.
  + move => h5.
    rewrite -h2 -h3.
    congr.
  + move => h5. 
    subst modValue{2}.
    apply wordint_to_intword in h2.
    apply wordint_to_intword in h3.
    rewrite /EqIntWord in h2.
    rewrite /EqIntWord in h3.
    subst tmp1{1}.
    by subst tmp_range{1}.
- seq 1 1 : (#[/:]pre /\ EqWordInt max_value{1} maxValue{2} /\ 0 <= maxValue{2} < W64.modulus).
  + wp.
    by skip.
  seq 1 1 : (EqWordInt range{1} range{2} /\
             0 < to_uint range{1} < W64.modulus /\
             EqWordInt tmp1{1} modValue{2} /\
             EqWordInt tmp_range{1} (range{2} - 1) /\
             tmp1{1} = tmp_range{1} /\
             EqWordInt max_value{1} maxValue{2} /\
             0 <= maxValue{2} < W64.modulus /\
             0 <= value{2} < W64.modulus /\
             EqWordInt tmp2{1} value{2}).
  + rnd W64.to_uint W64.of_int.
    skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
    split.
    * move => vR h12.
      rewrite to_uint_small.   
      smt.
      reflexivity.
    * move => h12.
      split.
      * move => vR h13.
        rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
        exact W64.to_uintK.
        move => a h14.
        rewrite to_uint_small.
        smt.
        reflexivity.
        rewrite to_uint_small.
        smt.
        by simplify.
      * move => vR tmp2L h13.
        rewrite supp_dinter.    
        have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
        + apply W64.to_uint_cmp.
        smt.
  seq 1 1 : (#pre).
  - while (EqWordInt max_value{1} maxValue{2} /\
           0 <= maxValue{2} < W64.modulus /\
           0 <= value{2} < W64.modulus /\
           EqWordInt tmp2{1} value{2}).
    * rnd W64.to_uint W64.of_int.  
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8.
      split.
      + move => vR h9.
        rewrite to_uint_small.   
        smt.
        reflexivity.
      + move => h9.
        split.
        + move => vR h10.
          rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
          exact W64.to_uintK.
          move => a h11.
          rewrite to_uint_small.
          smt.
          reflexivity.
          rewrite to_uint_small.
          smt.
          by simplify.
        + move => vR tmp2L h10.
          split.
          + rewrite supp_dinter.    
            have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
            * apply W64.to_uint_cmp.
            smt.
          + move => h11.
            do! split.
            + smt.
            + smt.
            + move => h12.
              rewrite -h1.
              smt.
            + move => h12.
              apply wordint_to_intword in h1.
              rewrite -h1.
              rewrite ultE to_uint_small.
              split.
              assumption. by move => h13 /=.
              assumption.
    * skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
      split.
      + move => h12.  
        rewrite /EqWordInt in h11.
        rewrite /EqWordInt in h6.
        rewrite -h11 -h6.
        by rewrite ultE in h12.
      + move => h12.
        apply wordint_to_intword in h11.
        rewrite /EqIntWord in h11.
        apply wordint_to_intword in h6.
        rewrite /EqIntWord in h6.
        rewrite -h11 -h6.
        rewrite ultE.
        rewrite to_uint_small.
        split. assumption. by move => ?.
        rewrite to_uint_small.
        smt.
        assumption.
  wp.
  skip.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11.
  rewrite /EqWordInt.
  apply wordint_to_intword in h5.
  rewrite /EqIntWord in h5.
  rewrite -h5.
  simplify.
  rewrite -h11.
  rewrite umodE /ulift2 to_uint_small to_uint_small.
  rewrite /EqWordInt in h1.
  rewrite -h1.
  smt().
  smt().
  smt().
  smt().
- seq 2 1 : (#[/:]pre /\ EqWordInt max_value{1} maxValue{2}).
  - wp.
    skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9.
    rewrite /EqWordInt to_uintB.
    assumption. 
    rewrite to_uintB.
    assumption.
    by rewrite -h4 h6 /=.
  seq 2 2 : (0 <= to_uint tmp2{1} /\
             range{2} < W64.modulus /\
             EqWordInt tmp2{1} value{2} /\
             EqWordInt (tmp_range{1} + W64.one) range{2}).
  - seq 1 1 : (0 <= to_uint tmp2{1} /\
               range{2} < W64.modulus /\
               EqWordInt max_value{1} maxValue{2} /\
               EqWordInt tmp2{1} value{2} /\
               EqWordInt (tmp_range{1} + W64.one) range{2}).
    - rnd W64.to_uint W64.of_int.
    skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    split.
    * move => vR h11.
      rewrite to_uint_small.   
      smt.
      reflexivity.
    * move => h12.
      split.
      * move => vR h13.
        rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
        exact W64.to_uintK.
        move => a h14.
        rewrite to_uint_small.
        smt.
        reflexivity.
        rewrite to_uint_small.
        smt.
        by simplify.
      * move => vR tmp2L h13.
        rewrite supp_dinter.    
        have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
        + apply W64.to_uint_cmp.
        split.
        * smt.
        * move => h14.
          split.
          * case eq.
            move => />.
          * split.
            * by rewrite -h1.
            * smt.
    while (EqWordInt max_value{1} maxValue{2} /\
           EqWordInt tmp2{1} value{2} /\
           EqWordInt (tmp_range{1} + W64.one) range{2}).
    * rnd W64.to_uint W64.of_int.  
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5.
      split.
      + move => vR h6.
        rewrite to_uint_small.   
        smt.
        reflexivity.
      + move => h6.
        split.
        + move => vR h7.
          rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
          exact W64.to_uintK.
          move => a h8.
          rewrite to_uint_small.
          smt.
          reflexivity.
          rewrite to_uint_small.
          smt.
          by simplify.
        + move => vR tmp2L h7.
          split.
          + rewrite supp_dinter.    
            have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
            * apply W64.to_uint_cmp.
            smt.
          + move => h8.
            do! split.
            + smt.
            + smt.
              skip.
              move => &m1 &m2 /> h1 h2 h3 h4 h5.
              do! split.
              + smt.
              + smt.                
       * smt.
wp.
skip.
move => &m1 &m2 [h1 [h2 [h3 h4]]].
rewrite /EqWordInt umodE /ulift2 to_uint_small.
split.
- by apply modn_ge0.
- move => h5.
  rewrite /EqWordInt in h4.
  rewrite h4.
  smt.
  by rewrite h3 h4.
qed.

(*lemma implementation_reference_equiv :
  equiv[M.generate_password ~ RPGRef.generate_password :
          policyFitsW64 policy{2} /\
          policyInMem Glob.mem{1} policy_addr{1} policy{2}
            ==>
          (res{1} \slt W64.zero <=> res{2} = None) /\
          (res{1} = W64.one <=> memPassword_eq_specPassword Glob.mem{1} W64.zero (oget res{2}))].*)
lemma implementation_reference_equiv :
  equiv [ConcreteScheme.generate_password ~ RPGRef.generate_password :
         ={policy} /\ policyFitsW64 policy{2} ==> ={res}].
proof.
proc.
admitted.
(*seq 3 0 : (#pre /\
           policyAddr{1} = W64.zero /\
           pwdAddr{1} = (of_int%W64 1000) /\ 
           policyInMem policy{1} Glob.mem{1} (W64.zero)).
sp.
(*ecall{1} (imp_policy_to_mem policy{1} Glob.mem{1} policyAddr{1}).*)
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
seq 84 4 : (#pre).
- inline *.
  auto.
  seq 26 0 : (#pre).
  - auto.
  seq 2 0 : (#pre).
  - sp.
    while{1} true (76 - to_uint i{1}).
    + move => &m z.
      wp. skip. smt.
      skip.
      smt.
  seq 26 0 : (#pre).
  - auto.
  seq 2 0 : (#pre).
  - sp.
    while{1} true (76 - to_uint i{1}).
    + move => &m z.
      wp. skip. smt.
      skip.
      smt.
  seq 10 0 : (#pre).
  - auto.
  seq 2 0 : (#pre).
  - sp.
    while{1} true (76 - to_uint i{1}).
    + move => &m z.
      wp. skip. smt.
      skip.
      smt.
  seq 14 0 : (#pre).
  - auto.
  seq 2 0 : (#pre).
  - sp.
    while{1} true (76 - to_uint i{1}).
    + move => &m z.
      wp. skip. smt.
      skip.
      smt.
  by skip.
seq 2 0 : (#pre).
- sp.
  while{1} true (76 - to_uint i{1}).
    + move => &m z.
      wp. skip. smt.
      skip.
      smt.
seq 1 1 : (#[/:]pre /\ generatedPassword{2} = [] /\
           size generatedPassword{2} = to_uint%W64 i_filled{1}).
- auto.
seq 0 4 : (#[/:]pre /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2}).
- auto.
  move => />.
seq 1 1 : ().
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
admitted.*)


(*********************************)
(*          CORRECTNESS          *)
(*********************************)

lemma concrete_rpg_correctness &m policy :
  policyFitsW64 policy =>
  Pr[Correctness(ConcreteScheme).main(policy) @ &m : res] = 1%r.
proof.
move => h1. 
have correct_ref : Pr[Correctness(RPGRef).main(policy) @ &m : res] = 1%r.
+ exact rpg_correctness.
rewrite -correct_ref.
byequiv.
proc.
wp.
call implementation_reference_equiv.
by skip.
trivial.
trivial.
qed.

(*********************************)
(*           SECURITY            *)
(*********************************)
