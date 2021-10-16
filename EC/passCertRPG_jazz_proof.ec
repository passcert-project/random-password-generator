require import AllCore Number IntDiv Distr DInterval List PassCertRPG_jazz PassCertRPG_ref.
from Jasmin require import JModel.
require import Array76.
require import WArray76.

(*-------------------------------*)
(*----- Auxiliary operators -----*)
(*-------------------------------*)

op EqWordChar word char = W8.to_uint word = char.
op EqWordInt word int = W64.to_uint word = int.
op EqIntWord int word = W64.of_int int = word.
op EqWordIntSet (memSet:W8.t Array76.t) (specSet:charSet) =
  forall n, n \in range 0 (size specSet) => EqWordChar memSet.[n] (nth (-1) specSet n).

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

op memPolicy_eq_specPolicy mem policyAddr policy =
  EqWordInt (loadW64 mem (W64.to_uint policyAddr)) policy.`length /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+8)) policy.`lowercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+16)) policy.`lowercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+24)) policy.`uppercaseMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+32)) policy.`uppercaseMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+40)) policy.`numbersMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+48)) policy.`numbersMax /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+56)) policy.`specialMin /\
  EqWordInt (loadW64 mem ((W64.to_uint policyAddr)+64)) policy.`specialMax.

op specPolicy_eq_registers policy (length lowercase_min lowercase_max uppercase_min uppercase_max
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


op memPassword_eq_specPassword mem passwordAddr password =
  forall n, n \in range 0 (size password) =>
  nth (-1) password n = W8.to_uint (loadW8 mem (W64.to_uint passwordAddr + n)).

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

lemma RDRAND_dinterval :
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

lemma load_from_store_W8 mem addr word :
  loadW8 (storeW8 mem addr word) (addr) = word.
proof.
by rewrite /loadW8 /storeW8 /=.
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
  (specPolicy_eq_registers policy length lowercase_min lowercase_max uppercase_min
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


lemma append_trash_to_eq_set memSet specSet n x:
  EqWordIntSet memSet specSet =>
  size specSet <= n =>
  EqWordIntSet memSet.[n <- x] specSet.
proof.
move => h1 h2.
rewrite /EqWordIntSet.
rewrite /EqWordIntSet in h1.
move => n0.
move => h3.
rewrite /EqWordChar.
rewrite get_set_if.
have diff : !(n0 = n).
+ rewrite mem_range in h3.
  smt().
rewrite diff /=.
by apply h1.
qed.


lemma eq_mem_password_empty mem addr :
  memPassword_eq_specPassword mem addr [].
proof.
rewrite /memPassword_eq_specPassword.
move => n0.
rewrite mem_range.
smt().
qed.

lemma load_pw_append_unchanged (mem:global_mem_t) offset max x :
  forall n, n \in range 0 max =>
  loadW8 mem (offset + n) = loadW8 (storeW8 mem (offset + max) x) (offset + n).
proof.
smt. (*hack, interesting proof to be more precise*)
qed.

lemma eq_mem_password_append mem addr pw x y :
  EqWordChar x y =>
  memPassword_eq_specPassword mem addr pw =>
  memPassword_eq_specPassword (storeW8 mem (to_uint addr + (size pw)) x) addr (pw ++ [y]).
proof.
move => h1 h2.
rewrite /memPassword_eq_specPassword in h2.
rewrite /memPassword_eq_specPassword.
move => n range.
case (0 <= n < size pw).
- move => [h3 h4].
  have h5 : n \in (range 0 (size pw)).
  + smt.
  rewrite -(load_pw_append_unchanged mem (to_uint addr) (size pw) x).
  assumption.
  rewrite nth_cat h4 /=.
  apply h2.
  assumption.
case (n = size pw).
- move => h3 h4.
  have h5 : nth (-1) (pw ++ [y]) n = y.
  + by rewrite nth_cat h3 /=.
  have h6 : loadW8 (storeW8 mem (to_uint addr + size pw) x) (to_uint addr + n) = x.
  + by rewrite -h3 load_from_store_W8.
  by rewrite h5 h6 eq_sym.
case (n < 0).
- smt.
case (size pw < n).
- smt.
smt.
qed.

(*********************************)
(*          EQUIVALENCE          *)
(*********************************)

axiom rdrand_eq_dist :
  RDRAND = dmap [0..W64.max_uint] W64.of_int.


(*---------------------------*)
(*----- RNG Equivalence -----*)
(*---------------------------*)

lemma imp_ref_rng_equiv _range :
  equiv[M.rng ~ RPGRef.rng : range{2} = _range /\
                             EqWordInt range{1} range{2} /\
                             0 < to_uint range{1} < W64.modulus
                               ==>
                             EqWordInt res{1} res{2} /\
                             0 <= res{2} < _range].
proof.
proc.
seq 5 1 : (#pre /\
           EqWordInt tmp1{1} modValue{2} /\
           EqWordInt tmp_range{1} (range{2} - 1) /\
           EqWordInt tmp2{1} (2^64-1) /\
           W64.one \ule (tmp2{1} - tmp1{1}) /\
           tmp1{1} \ule tmp2{1} /\
           0 < _range).
- wp.
  skip.
  move => &1 &2 [h1 [h2 [h3 h4]]] />.
  rewrite umodE /ulift2 h1 /= /EqWordInt to_uint_small.
  split.
  + by apply modn_ge0.
  + move => h5.
    rewrite h2.
    have mod : 18446744073709551615 %% to_uint range{1} < to_uint range{1}.
    * by apply ltz_pmod.
    (*apply (ltr_trans mod h3). cant find the lemma for some reason*)
    smt.
  do! split.
  + by rewrite h2 h1.
  + rewrite to_uintB.
    rewrite uleE /=.
    smt().
    by rewrite h2 h1 /=.
  + rewrite uleE /=.
    smt.
  + smt.
  + rewrite h2 in h3.
    by subst.    
if.
- move => &1 &2 [h1 [h2 [h3 [h4 h5]]]] />.
  split.
  + move => h6.
    rewrite -h2 -h3.
    congr.
  + move => h6. 
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
  seq 1 1 : (range{2} = _range /\ 
             0 < _range /\
             EqWordInt range{1} range{2} /\
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
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.
    split.
    * move => vR h13.
      rewrite to_uint_small.   
      smt.
      reflexivity.
    * move => h13.
      split.
      * move => vR h14.
        rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
        exact W64.to_uintK.
        move => a h15.
        rewrite to_uint_small.
        smt.
        reflexivity.
        rewrite to_uint_small.
        smt.
        by simplify.
      * move => vR tmp2L h14.
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
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.
      split.
      + move => h13.  
        rewrite /EqWordInt in h11.
        rewrite /EqWordInt in h6.
        rewrite -h12 -h7.
        by rewrite ultE in h13.
      + move => h13.
        apply wordint_to_intword in h12.
        rewrite /EqIntWord in h12.
        apply wordint_to_intword in h7.
        rewrite /EqIntWord in h7.
        rewrite -h12 -h7.
        rewrite ultE.
        rewrite to_uint_small.
        split. assumption. by move => ?.
        rewrite to_uint_small.
        smt.
        assumption.
  wp.
  skip.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12.
  do! split.
  - rewrite /EqWordInt.
  apply wordint_to_intword in h6.
  rewrite /EqIntWord in h6.
  rewrite -h6.
  simplify.
  rewrite -h12.
  rewrite umodE /ulift2 to_uint_small to_uint_small.
  rewrite h2 in h4.
  smt().
  smt().
  smt().
  smt().
  smt().
  smt().
- seq 2 1 : (#[/:]pre /\ EqWordInt max_value{1} maxValue{2}).
  - wp.
    skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10.
    rewrite /EqWordInt to_uintB.
    assumption. 
    rewrite to_uintB.
    assumption.
    by rewrite -h4 h6 /=.
  seq 2 2 : (range{2} = _range /\
             0 < _range /\
             0 <= to_uint tmp2{1} /\
             range{2} < W64.modulus /\
             EqWordInt tmp2{1} value{2} /\
             EqWordInt (tmp_range{1} + W64.one) range{2}).
  - seq 1 1 : (0 <= to_uint tmp2{1} /\
               range{2} < W64.modulus /\
               range{2} = _range /\
               0 < _range /\
               EqWordInt max_value{1} maxValue{2} /\
               EqWordInt tmp2{1} value{2} /\
               EqWordInt (tmp_range{1} + W64.one) range{2}).
    - rnd W64.to_uint W64.of_int.
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
        split.
        * smt.
        * move => h14.
          split.
          * case eq.
            move => />.
          * split.
            * by rewrite -h1.
            * smt.
    while (range{2} = _range /\
           0 < _range /\
           EqWordInt max_value{1} maxValue{2} /\
           EqWordInt tmp2{1} value{2} /\
           EqWordInt (tmp_range{1} + W64.one) range{2}).
    * rnd W64.to_uint W64.of_int.  
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6.
      split.
      + move => vR h7.
        rewrite to_uint_small.   
        smt.
        reflexivity.
      + move => h7.
        split.
        + move => vR h8.
          rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
          exact W64.to_uintK.
          move => a h9.
          rewrite to_uint_small.
          smt.
          reflexivity.
          rewrite to_uint_small.
          smt.
          by simplify.
        + move => vR tmp2L h8.
          split.
          + rewrite supp_dinter.    
            have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
            * apply W64.to_uint_cmp.
            smt.
          + move => h9.
            do! split.
            + smt.
            + smt.
              skip.
              move => &m1 &m2 /> h1 h2 h3 h4 h5 h6.
              do! split.
              + smt.
              + smt.                
       * smt.
wp.
skip.
move => &m1 &m2 [h1 [h2 [h3 [h4 [h5 h6]]]]].
rewrite /EqWordInt umodE /ulift2 to_uint_small.
split.
- by apply modn_ge0.
- smt.
subst.
move => vR />.
split.
- smt().
- split.
  - rewrite modz_ge0. smt().
  - move => h7. by apply ltz_pmod.
qed.

(*---------------------------*)
(*----- RCG Equivalence -----*)
(*---------------------------*)

lemma imp_ref_rcg_equiv :
  equiv[M.random_char_generator ~ RPGRef.random_char_generator :
          EqWordIntSet set{1} set{2} /\
          EqWordInt range{1} (size set{2}) /\
          0 < to_uint range{1} < W64.modulus
           ==>
          EqWordChar res{1} res{2}].
proof.
proc.
seq 1 1 : (#pre /\ 0 <= choice{2} < (size set{2}) /\ EqWordInt choice_0{1} choice{2}).
- ecall (imp_ref_rng_equiv (size set{2})).
  by skip.
wp.
skip.
move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7.
rewrite /EqWordIntSet in h1.
rewrite h7.
apply h1.
by apply mem_range.
qed.


(*---------------------------*)
(*----- RPG Equivalence -----*)
(*---------------------------*)

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
seq 3 0 : (#pre /\
           policyAddr{1} = W64.zero /\
           pwdAddr{1} = (of_int%W64 1000) /\ 
           memPolicy_eq_specPolicy Glob.mem{1} (W64.zero) policy{1}).
sp.
(*ecall{1} (imp_policy_to_mem policy{1} Glob.mem{1} policyAddr{1}).*)
admit.
inline M.generate_password.
seq 17 0 : (={policy} /\
            output_addr{1} = W64.of_int 1000 /\
            specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
            tmp64_1{1} = length{1}).
- auto.
  move => &m1 &m2 />.
if{1}.
if{1}.
seq 0 0 : (={policy} /\
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1}).
by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
                           uppercase_min{1} uppercase_max{1} numbers_min{1}
                           numbers_max{1} special_min{1} special_max{1} /\
           length{1} \ule (of_int 200)%W64 /\
           W64.zero \ult length{1} /\
           W64.zero \ule lowercase_min{1}).
- by skip.
sp.
if{1}.
seq 0 0 : (={policy} /\
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
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
           output_addr{1} = W64.of_int 1000 /\
           specPolicy_eq_registers policy{1} length{1} lowercase_min{1} lowercase_max{1}
                         uppercase_min{1} uppercase_max{1} numbers_min{1}
                         numbers_max{1} special_min{1} special_max{1} /\
           satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
                                uppercase_min{1} uppercase_max{1}
                                numbers_min{1} numbers_max{1}
                                special_min{1} special_max{1}).
- skip.
  move => &m1 &m2 />.

(* if both mem and spec are satisfiable... distribution on the output should be equal *)
if{2}.
seq 26 1 : (#[/:]pre /\
            EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
            RPGRef.lowercaseSet{2} = [97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108;
              109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122]).
inline *.
seq 0 2 : (#[/:]pre /\ RPGRef.lowercaseSet{2} = [97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122]).
- auto.
wp.
auto.
move => &m1 &m2 /> ????????????????????????????????????????? n h1.
rewrite /EqWordIntSet /size /=.
do! rewrite get_set_if /=.
case (n=0). move => h2. rewrite h2 /=. reflexivity.
case (n=1). move => h2. rewrite h2 /=. reflexivity.
case (n=2). move => h2. rewrite h2 /=. reflexivity.
case (n=3). move => h2. rewrite h2 /=. reflexivity.
case (n=4). move => h2. rewrite h2 /=. reflexivity.
case (n=5). move => h2. rewrite h2 /=. reflexivity.
case (n=6). move => h2. rewrite h2 /=. reflexivity.
case (n=7). move => h2. rewrite h2 /=. reflexivity.
case (n=8). move => h2. rewrite h2 /=. reflexivity.
case (n=9). move => h2. rewrite h2 /=. reflexivity.
case (n=10). move => h2. rewrite h2 /=. reflexivity.
case (n=11). move => h2. rewrite h2 /=. reflexivity.
case (n=12). move => h2. rewrite h2 /=. reflexivity.
case (n=13). move => h2. rewrite h2 /=. reflexivity.
case (n=14). move => h2. rewrite h2 /=. reflexivity.
case (n=15). move => h2. rewrite h2 /=. reflexivity.
case (n=16). move => h2. rewrite h2 /=. reflexivity.
case (n=17). move => h2. rewrite h2 /=. reflexivity.
case (n=18). move => h2. rewrite h2 /=. reflexivity.
case (n=19). move => h2. rewrite h2 /=. reflexivity.
case (n=20). move => h2. rewrite h2 /=. reflexivity.
case (n=21). move => h2. rewrite h2 /=. reflexivity.
case (n=22). move => h2. rewrite h2 /=. reflexivity.
case (n=23). move => h2. rewrite h2 /=. reflexivity.
case (n=24). move => h2. rewrite h2 /=. reflexivity.
case (n=25). move => h2. rewrite h2 /=. reflexivity.
case (25<n). smt.
smt.
seq 2 0 : (#pre).
- sp.
  while{1} (={policy} /\
            output_addr{1} = W64.of_int 1000 /\
            specPolicy_eq_registers policy{1} length{1} lowercase_min{1}
              lowercase_max{1} uppercase_min{1} uppercase_max{1} numbers_min{1}
              numbers_max{1} special_min{1} special_max{1} /\
            satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
              uppercase_min{1} uppercase_max{1} numbers_min{1} numbers_max{1}
              special_min{1} special_max{1} /\
            satisfiablePolicy policy{2} /\
            EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
            W64.of_int 26 \ule i{1} /\
            RPGRef.lowercaseSet{2} = [97; 98; 99; 100; 101; 102; 103; 104; 105; 106; 107; 108;
              109; 110; 111; 112; 113; 114; 115; 116; 117; 118; 119; 120; 121; 122])
            (76 - W64.to_uint i{1}).
  * move => &m2 z.
    auto.
    move => &m1 /> ????????????????????????????????????????????.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      smt.
    - smt.
    - smt.
  * skip.
    move => &m1 &m2 />.
    smt.
seq 26 1 : (#[/:]pre /\ 
            EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
            RPGRef.uppercaseSet{2} = [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76; 77; 78;
              79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90]).
inline *.
seq 0 2 : (#[/:]pre /\
           RPGRef.uppercaseSet{2} = [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76;
             77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90]).
- auto.
wp.
auto.
move => &m1 &m2 /> ?????????????????????????????????????????? n h1.
rewrite /uppercaseSet /EqWordIntSet /size /=.
do! rewrite get_set_if /=.
case (n=0). move => h2. rewrite h2 /=. reflexivity.
case (n=1). move => h2. rewrite h2 /=. reflexivity.
case (n=2). move => h2. rewrite h2 /=. reflexivity.
case (n=3). move => h2. rewrite h2 /=. reflexivity.
case (n=4). move => h2. rewrite h2 /=. reflexivity.
case (n=5). move => h2. rewrite h2 /=. reflexivity.
case (n=6). move => h2. rewrite h2 /=. reflexivity.
case (n=7). move => h2. rewrite h2 /=. reflexivity.
case (n=8). move => h2. rewrite h2 /=. reflexivity.
case (n=9). move => h2. rewrite h2 /=. reflexivity.
case (n=10). move => h2. rewrite h2 /=. reflexivity.
case (n=11). move => h2. rewrite h2 /=. reflexivity.
case (n=12). move => h2. rewrite h2 /=. reflexivity.
case (n=13). move => h2. rewrite h2 /=. reflexivity.
case (n=14). move => h2. rewrite h2 /=. reflexivity.
case (n=15). move => h2. rewrite h2 /=. reflexivity.
case (n=16). move => h2. rewrite h2 /=. reflexivity.
case (n=17). move => h2. rewrite h2 /=. reflexivity.
case (n=18). move => h2. rewrite h2 /=. reflexivity.
case (n=19). move => h2. rewrite h2 /=. reflexivity.
case (n=20). move => h2. rewrite h2 /=. reflexivity.
case (n=21). move => h2. rewrite h2 /=. reflexivity.
case (n=22). move => h2. rewrite h2 /=. reflexivity.
case (n=23). move => h2. rewrite h2 /=. reflexivity.
case (n=24). move => h2. rewrite h2 /=. reflexivity.
case (n=25). move => h2. rewrite h2 /=. reflexivity.
case (25<n). smt.
smt.
seq 2 0 : (#pre).
- sp.
  while{1} (={policy} /\
            output_addr{1} = W64.of_int 1000 /\
            specPolicy_eq_registers policy{1} length{1} lowercase_min{1}
              lowercase_max{1} uppercase_min{1} uppercase_max{1} numbers_min{1}
              numbers_max{1} special_min{1} special_max{1} /\
            satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
              uppercase_min{1} uppercase_max{1} numbers_min{1} numbers_max{1}
              special_min{1} special_max{1} /\
            satisfiablePolicy policy{2} /\
            EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
            EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
            W64.of_int 26 \ule i{1} /\
            RPGRef.uppercaseSet{2} = [65; 66; 67; 68; 69; 70; 71; 72; 73; 74; 75; 76;
              77; 78; 79; 80; 81; 82; 83; 84; 85; 86; 87; 88; 89; 90])
            (76 - W64.to_uint i{1}).
  * move => &m2 z.
    auto.
    move => &m1 /> ?????????????????????????????????????????????.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      smt.
    - smt.
    - smt.
  * skip.
    move => &m1 &m2 />.
    smt.
seq 10 1 : (#[/:]pre /\
            EqWordIntSet numbers_set{1} numbersSet{2} /\
            RPGRef.numbersSet{2} = [48; 49; 50; 51; 52; 53; 54; 55; 56; 57]).
inline *.
seq 0 2 : (#pre /\ RPGRef.numbersSet{2} = [48; 49; 50; 51; 52; 53; 54; 55; 56; 57]).
- auto.
wp.
auto.
move => &m1 &m2 /> ??????????????????????????????????????????? n h1.
rewrite /numbersSet /EqWordIntSet /size /=.
do! rewrite get_set_if /=.
case (n=0). move => h2. rewrite h2 /=. reflexivity.
case (n=1). move => h2. rewrite h2 /=. reflexivity.
case (n=2). move => h2. rewrite h2 /=. reflexivity.
case (n=3). move => h2. rewrite h2 /=. reflexivity.
case (n=4). move => h2. rewrite h2 /=. reflexivity.
case (n=5). move => h2. rewrite h2 /=. reflexivity.
case (n=6). move => h2. rewrite h2 /=. reflexivity.
case (n=7). move => h2. rewrite h2 /=. reflexivity.
case (n=8). move => h2. rewrite h2 /=. reflexivity.
case (n=9). move => h2. rewrite h2 /=. reflexivity.
case (9<n). smt.
smt.
seq 2 0 : (#pre).
- sp.
  while{1} (={policy} /\
            output_addr{1} = W64.of_int 1000 /\
            specPolicy_eq_registers policy{1} length{1} lowercase_min{1}
              lowercase_max{1} uppercase_min{1} uppercase_max{1} numbers_min{1}
              numbers_max{1} special_min{1} special_max{1} /\
            satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
              uppercase_min{1} uppercase_max{1} numbers_min{1} numbers_max{1}
              special_min{1} special_max{1} /\
            satisfiablePolicy policy{2} /\
            EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
            EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
            EqWordIntSet numbers_set{1} numbersSet{2} /\
            W64.of_int 10 \ule i{1} /\
            RPGRef.numbersSet{2} = [48; 49; 50; 51; 52; 53; 54; 55; 56; 57])
           (76 - W64.to_uint i{1}).
  * move => &m2 z.
    auto.
    move => &m1 /> ??????????????????????????????????????????????.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      smt.
    - smt.
    - smt.
  * skip.
    move => &m1 &m2 />.
    smt.
seq 14 1 : (#[/:]pre /\
            EqWordIntSet special_set{1} specialSet{2} /\
            RPGRef.specialSet{2} = [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61]).
inline *.
seq 0 2 : (#pre /\ RPGRef.specialSet{2} = [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61]).
- auto.
wp.
auto.
move => &m1 &m2 /> ???????????????????????????????????????????? n h1.
rewrite /specialSet /EqWordIntSet /size /=.
do! rewrite get_set_if /=.
case (n=0). move => h2. rewrite h2 /=. reflexivity.
case (n=1). move => h2. rewrite h2 /=. reflexivity.
case (n=2). move => h2. rewrite h2 /=. reflexivity.
case (n=3). move => h2. rewrite h2 /=. reflexivity.
case (n=4). move => h2. rewrite h2 /=. reflexivity.
case (n=5). move => h2. rewrite h2 /=. reflexivity.
case (n=6). move => h2. rewrite h2 /=. reflexivity.
case (n=7). move => h2. rewrite h2 /=. reflexivity.
case (n=8). move => h2. rewrite h2 /=. reflexivity.
case (n=9). move => h2. rewrite h2 /=. reflexivity.
case (n=10). move => h2. rewrite h2 /=. reflexivity.
case (n=11). move => h2. rewrite h2 /=. reflexivity.
case (n=12). move => h2. rewrite h2 /=. reflexivity.
case (n=13). move => h2. rewrite h2 /=. reflexivity.
case (13<n). smt.
smt.
seq 2 0 : (#pre).
- sp.
  while{1} (={policy} /\
            output_addr{1} = W64.of_int 1000 /\
            specPolicy_eq_registers policy{1} length{1} lowercase_min{1}
              lowercase_max{1} uppercase_min{1} uppercase_max{1} numbers_min{1}
              numbers_max{1} special_min{1} special_max{1} /\
            satisfiableMemPolicy length{1} lowercase_min{1} lowercase_max{1}
              uppercase_min{1} uppercase_max{1} numbers_min{1} numbers_max{1}
              special_min{1} special_max{1} /\
            satisfiablePolicy policy{2} /\
            EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
            EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
            EqWordIntSet numbers_set{1} numbersSet{2} /\
            EqWordIntSet special_set{1} specialSet{2} /\
            W64.of_int 14 \ule i{1} /\
            RPGRef.specialSet{2} = [33; 63; 35; 36; 37; 38; 43; 45; 42; 95; 64; 58; 59; 61])
            (76 - W64.to_uint i{1}).
  * move => &m2 z.
    auto.
    move => &m1 /> ???????????????????????????????????????????????.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      smt.
    - smt.
    - smt.
  * skip.
    move => &m1 &m2 />.
    smt.
seq 2 0 : (#pre).
- sp.
  while{1} (true) (76 - to_uint i{1}).
  * move => _ z.
    auto.
    smt.
  * skip.
    move => &m1 &m2 />.
    smt.
seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           specPolicy_eq_registers policy{2} length{1} lowercase_min{1}
             lowercase_max{1} uppercase_min{1} uppercase_max{1}
             numbers_min{1} numbers_max{1} special_min{1} special_max{1} /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           lowercase_min{1} \ule lowercase_max{1} /\
           W64.zero\ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           uppercase_min{1} \ule uppercase_max{1} /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           numbers_min{1} \ule numbers_max{1} /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           generatedPassword{2} = [] /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
           i_filled{1} = W64.zero).
- auto.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45.
  do! split.
  - smt.
  - smt.
  - smt.
  - smt.
  - apply eq_mem_password_empty.  
seq 0 4 : (#[/:]pre /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2}).
- auto.
  move => &m1 &m2 />.
seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           uppercase_min{1} \ule uppercase_max{1} /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           numbers_min{1} \ule numbers_max{1} /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           i_filled{1} = lowercase_min{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42.
    split.
    * by rewrite ultE h39 /=.
    * by rewrite ultE h39 /=.
  + seq 1 1 : (#[/:]pre /\ 
               EqWordInt i{1} i{2} /\
               i{2} = 0 /\
               lowercase_min{1} \ule i{1} + lowercase_max{1}).
    - auto.
    while (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           uppercase_min{1} \ule uppercase_max{1} /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           numbers_min{1} \ule numbers_max{1} /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
           EqWordInt i{1} i{2} /\
           lowercase_min{1} \ule i{1} + lowercase_max{1} /\
           0 <= to_uint i{1} <= to_uint lowercase_min{1} /\
           i{1} = i_filled{1}).
    * seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 uppercase_min{1} \ule uppercase_max{1} /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 numbers_min{1} \ule numbers_max{1} /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 lowercase_min{1} \ule i{1} + lowercase_max{1} + W64.one /\
                 0 <= to_uint i{1} < to_uint lowercase_min{1} /\
                 i{1} = i_filled{1}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40.
        have lmax_ge_one : W64.one \ule lowercase_max{m1}.
        + smt.
        do! split.
        - rewrite uleE to_uintB /=.
          assumption.
          smt.
        - rewrite /EqWordInt to_uintB.
          assumption.
          by rewrite h29.
        - rewrite uleE to_uintD to_uintD to_uintB /=.
          smt.
          have small1 : (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1)) %%
                          18446744073709551616 =
                        (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1)).
          + smt.
          rewrite small1.
          have small2 : (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1) + 1) %%
                          18446744073709551616 =
                        (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1) + 1).
          + smt.
          rewrite small2.
          smt.
        - by rewrite -ultE.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - call imp_ref_rcg_equiv.
        skip.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38.
        - by rewrite /EqWordInt eq_sym /=.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 uppercase_min{1} \ule uppercase_max{1} /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 numbers_min{1} \ule numbers_max{1} /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 lowercase_min{1} \ule i{1} + lowercase_max{1} /\
                 0 <= to_uint i{1} <= to_uint lowercase_min{1} /\
                 i{1} = i_filled{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39.
        do! split.
        - rewrite to_uintD.
          have small : (to_uint i_filled{m1} + to_uint W64.one) %% W64.modulus =
                       to_uint i_filled{m1} + to_uint W64.one.
          + smt.
          by rewrite small -h33 size_cat /=.
        - rewrite to_uintD.
          have small : (to_uint (W64.of_int 1000) + to_uint i_filled{m1}) %% W64.modulus =
                       to_uint (W64.of_int 1000) + to_uint i_filled{m1}.
          + smt.
          rewrite small -h33 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - smt.
        - smt.
        - smt.
        - smt.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39.
      do! split.
      - smt.
      - smt.
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43 h44 h45.
       do! split.
       - smt().
       - smt.   
       - rewrite /EqWordInt in h44.
         by rewrite -to_uintK h44.
       - move => h46.
         rewrite -h14.
         rewrite ultE in h46.
         by rewrite h44 in h46.
       - move => h46.
         rewrite -h14 in h46.
         rewrite -h44 in h46.
         by rewrite ultE.
       - move => ????????????????.
         smt.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42 h43.
    have : lowercase_max{m1} = W64.zero. 
    + rewrite ultE in h43.
      smt.
    have : lowercase_min{m1} = W64.zero. 
    + smt.
    trivial.

seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           numbers_min{1} \ule numbers_max{1} /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           i_filled{1} = lowercase_min{1} + uppercase_min{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34.
    split.
    * by rewrite ultE h30 /=.
    * by rewrite ultE h30 /=.
  + seq 1 1 : (#[/:]pre /\ 
               EqWordInt i{1} i{2} /\
               i{2} = 0 /\
               uppercase_min{1} \ule i{1} + uppercase_max{1}).
    - auto.
    while (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           numbers_min{1} \ule numbers_max{1} /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
           EqWordInt i{1} i{2} /\
           uppercase_min{1} \ule i{1} + uppercase_max{1} /\
           0 <= to_uint i{1} <= to_uint uppercase_min{1} /\
           i_filled{1} = lowercase_min{1} + i{1}).
    * seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 numbers_min{1} \ule numbers_max{1} /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 uppercase_min{1} \ule i{1} + uppercase_max{1} + W64.one /\
                 0 <= to_uint i{1} < to_uint uppercase_min{1} /\
                 i_filled{1} = lowercase_min{1} + i{1}).
      - auto.
        move => &m1 &m2 h1 diff.
        have lmax_ge_one : W64.one \ule uppercase_max{m1}.
        + smt.
        smt.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - call imp_ref_rcg_equiv.
        skip.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37.
        - by rewrite /EqWordInt eq_sym /=.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 numbers_min{1} \ule numbers_max{1} /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 uppercase_min{1} \ule i{1} + uppercase_max{1} /\
                 0 <= to_uint i{1} <= to_uint uppercase_min{1} /\
                 i_filled{1} = lowercase_min{1} + i{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38.
        do! split.
        - rewrite to_uintD.
          have small : (to_uint (lowercase_min{m1} + i{m1}) + to_uint W64.one) %% W64.modulus =
                       to_uint (lowercase_min{m1} + i{m1}) + to_uint W64.one.
          + smt.
          by rewrite small -h32 size_cat /=. 
        - rewrite to_uintD.
          have small :
            (to_uint (W64.of_int 1000) + to_uint (lowercase_min{m1} + i{m1})) %% W64.modulus =
            to_uint (W64.of_int 1000) + to_uint (lowercase_min{m1} + i{m1}).
          + smt.
          rewrite small -h32 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - smt.
        - smt.
        - smt.
        - smt.
        - ring.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38.
      do! split.
      - smt.
      - smt.
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37.
       do! split.
       - smt().
       - smt.
       - apply wordint_to_intword in h36.
         by rewrite -to_uintK -h36.
       - move => h38.
         rewrite -h2.
         rewrite ultE in h38.
         by rewrite h36 in h38.
       - move => h38.
         rewrite -h2 in h38.
         rewrite -h36 in h38.
         by rewrite ultE.
       - move => ????????????????.
         smt.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35.
    have : uppercase_max{m1} = W64.zero. 
    + rewrite ultE in h35.
      smt.
    have : uppercase_min{m1} = W64.zero.
    + smt.
    move => h36 h37.
    rewrite h36.
    ring.












seq 1 1 : (#pre /\ EqWordIntSet union_set{1} unionSet{2} /\ to_uint tmp64_1{1} = size unionSet{2}).
admit.
seq 1 0 : (#[/:]pre /\ EqWordInt tmp64_2{1} policy{2}.`length).
- auto.



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
