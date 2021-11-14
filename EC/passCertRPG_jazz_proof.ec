require import AllCore IntDiv Distr DInterval List PassCertRPG_jazz PassCertRPG_ref
               Ring IntDiv StdOrder UpdateList.
import Ring.IntID IntOrder.
from Jasmin require import JModel.
require import Number.
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
      i <- i + 1;
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
 RDRAND = dmap [0..W64.max_uint] W64.of_int.
proof.
rewrite /RDRAND /dword.
apply eq_distr => x.
rewrite duniform1E dmap1E all_wordsP /= /all_words.
rewrite undup_id.
 rewrite map_inj_in_uniq.
  move=> a b Ha Hb H.
 have: W64.to_uint (W64.of_int a) = W64.to_uint (W64.of_int b) by smt().
  rewrite !of_uintK !modz_small.
  rewrite mem_iota /= in Ha. case Ha. move => Ha1 Ha2.
  split. assumption. by rewrite /absz /=.
  rewrite mem_iota /= in Hb. case Hb. move => Hb1 Hb2.
  split. assumption. by rewrite /absz /=.
  trivial.
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

lemma load_storeW64_neq mem a1 a2 word:
 (a2 + 8 <= a1 || a1 + 8 <= a2) => 
 loadW64 mem a2 = loadW64 (storeW64 mem a1 word) a2.
proof.
move => H; rewrite /loadW64 /storeW64; congr.
apply W8u8.Pack.all_eq_eq; rewrite /all_eq !storesE /=.
rewrite !get_setE => |>. smt(). 
qed.

lemma load_pw_append_unchanged (mem:global_mem_t) offset max x :
  forall n, n \in range 0 max =>
  loadW8 mem (offset + n) = loadW8 (storeW8 mem (offset + max) x) (offset + n).
proof.
admit.
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
    have : to_uint lowercase_min <= 200.
    + smt(@Number).
    have : to_uint uppercase_min <= 200.
    + smt(@Number).
    have : to_uint numbers_min <= 200.
    + smt(@Number).
    have : to_uint special_min <= 200.
    + smt(@Number).
    have : to_uint (lowercase_min + uppercase_min) <= 400.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?????.
    have : to_uint (lowercase_min + uppercase_min + numbers_min) <= 600.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    rewrite -to_uintD_small. smt(@Number).
    rewrite -to_uintD_small. smt(@Number).
    rewrite -to_uintD_small. smt(@Number).
    assumption.
  - rewrite -h3 -h5 -h7 -h9 -h1.
    have : to_uint (lowercase_max + uppercase_max) <= 400.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    have : to_uint (lowercase_max + uppercase_max + numbers_max) <= 600.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    rewrite -to_uintD_small. smt(@Number).
    rewrite -to_uintD_small. smt(@Number).
    rewrite -to_uintD_small. smt(@Number).
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
    have : to_uint lowercase_min <= 200.
    + smt(@Number).
    have : to_uint uppercase_min <= 200.
    + smt(@Number).
    have : to_uint numbers_min <= 200.
    + smt(@Number).
    have : to_uint special_min <= 200.
    + smt(@Number).
    have : to_uint (lowercase_min + uppercase_min) <= 400.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?????.
    have : to_uint (lowercase_min + uppercase_min + numbers_min) <= 600.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    rewrite to_uintD_small. smt(@Number).
    rewrite to_uintD_small. smt(@Number).
    rewrite to_uintD_small. smt(@Number).
    assumption.
  - rewrite -h1 -h3 -h5 -h7 -h9 in h25.
    rewrite uleE.
    have : to_uint (lowercase_max + uppercase_max) <= 400.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    have : to_uint (lowercase_max + uppercase_max + numbers_max) <= 600.
    + rewrite to_uintD_small.
      smt(@Number).
      smt(@Number).
    move => ?.
    rewrite to_uintD_small. smt(@Number).
    rewrite to_uintD_small. smt(@Number).
    rewrite to_uintD_small. smt(@Number).
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
  + smt(@List).
  rewrite -(load_pw_append_unchanged mem (to_uint addr) (size pw) x).
  assumption.
  rewrite nth_cat h4 /=.
  apply h2.
  assumption.
case (n = size pw).
- move => h3 h4.
  have h5 : !(n < size pw).
  + smt().
  have h6 : nth (-1) (pw ++ [y]) n = y.
  + rewrite nth_cat h5 /=. smt().
  have h7 : loadW8 (storeW8 mem (to_uint addr + size pw) x) (to_uint addr + n) = x.
  + by rewrite -h3 load_from_store_W8.
  by rewrite h6 h7 eq_sym.
case (size pw < n).
- have : 0 <= n < size (pw ++ [y]).
  + apply mem_range.
    smt().
  move => [h3 h4] h5 h6 h7.
  have h8 : size (pw ++ [y]) = size pw + 1.
  + by rewrite size_cat.
  smt().
case (n < 0).
- have : 0 <= n.
  + smt(@List).
  smt().
smt().
qed.


lemma eq_set_append (memSet:W8.t Array76.t) (specSet:charSet)
                    (appMemSet:W8.t Array76.t) (appSpecSet:charSet) (x:char) :
  0 <= size specSet < 76 =>
  EqWordIntSet memSet specSet =>
  EqWordChar appMemSet.[0] (head x appSpecSet) =>
  EqWordIntSet (memSet.[size specSet <- appMemSet.[0]]) (specSet ++ [head x appSpecSet]).
proof.  
rewrite /EqWordIntSet.
move => h1 h2 h3.
rewrite size_cat /=.
move => n. rewrite mem_range. move => [h4 h5].
rewrite get_set_if h1 /=.
case (n = size specSet).
+ move => h6.
  rewrite nth_cat.
  have : !(n < size specSet).
  + smt().
  move => h7. rewrite h7 /=.
  have ss : size specSet - size specSet = 0.
  + ring.
  by rewrite h6 ss /=.
+ move => h6.
  rewrite nth_cat.
  have : n < size specSet.
  + smt().
  move => h7. rewrite h7 /=.
  apply h2.  
  rewrite mem_range.
  smt().
qed.

lemma pwdMemToSpec_eq mem addr length pw :
  hoare[ConcreteScheme.pwdMemToSpec :
        length = size pw /\
        memPassword_eq_specPassword mem addr pw
        ==>
        res = pw].
proof.
proc.
sp.
while (i = size pwd /\
       memPassword_eq_specPassword mem addr pw /\
       forall (n:int), n \in range 0 i => nth (-1) pw n = nth (-1) pwd n).
+ auto.
  move => &m /> h1 h2 h3.
  split.
  - by rewrite size_cat /=.
  - move => n h4.
    rewrite mem_range in h4.
    case (0 <= n < size pwd{m}).
    - admit. admit.

+ auto.
  move => &m /> h1.
  split.
  - rewrite range_geq. trivial.
    trivial.
  - move => pwd h2 h3.  
    admit.
qed.

(*********************************)
(*          EQUIVALENCE          *)
(*********************************)

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
    rewrite /EqWordInt in h2.
    rewrite h2 in h4.
    smt().
  do! split.
  + by rewrite h2 h1.
  + rewrite to_uintB.
    rewrite uleE /=.
    smt().
    by rewrite h2 h1 /=.
  + rewrite uleE /=.
    have : 1 <= 18446744073709551615 - 18446744073709551615 %% to_uint range{1}.
    + smt.
    rewrite to_uint_small. smt().
    trivial.
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
      rewrite -mem_range.
      have supp : 0 <= vR <= 18446744073709551615.
      + by apply supp_dinter.
      rewrite mem_range.
      smt().
      reflexivity.
    * move => h13.
      split.
      * move => vR h14.
        rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
        exact W64.to_uintK.
        move => a h15.
        rewrite to_uint_small.
        have supp : 0 <= a <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
        reflexivity.
        rewrite to_uint_small.
        have supp : 0 <= vR <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
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
        have supp : 0 <= vR <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
        reflexivity.
      + move => h9.
        split.
        + move => vR h10.
          rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
          exact W64.to_uintK.
          move => a h11.
          rewrite to_uint_small.
          have supp : 0 <= a <= 18446744073709551615.
          + by apply supp_dinter.
          smt().
          reflexivity.
          rewrite to_uint_small.
          have supp : 0 <= vR <= 18446744073709551615.
          + by apply supp_dinter.
          smt().
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
      have supp : 0 <= vR <= 18446744073709551615.
      + by apply supp_dinter.
      smt().
      reflexivity.
    * move => h12.
      split.
      * move => vR h13.
        rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
        exact W64.to_uintK.
        move => a h14.
        rewrite to_uint_small.
        have supp : 0 <= a <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
        reflexivity.
        rewrite to_uint_small.
        have supp : 0 <= vR <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
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
            * rewrite /EqWordInt in h5.
              rewrite h1 in h3.
              rewrite /EqWordInt to_uintD /=.
              have : (to_uint tmp_range{m1} + 1) < 18446744073709551616.
              + smt().
              have : (to_uint tmp_range{m1} + 1) %% 18446744073709551616 =
                     (to_uint tmp_range{m1} + 1).
              + rewrite pmod_small.
              smt().
              reflexivity.
              move => h15 h16.
              rewrite h5 /= /#.
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
        have supp : 0 <= vR <= 18446744073709551615.
        + by apply supp_dinter.
        smt().
        reflexivity.
      + move => h7.
        split.
        + move => vR h8.
          rewrite RDRAND_dinterval (dmap1E_can [0..W64.max_uint] W64.of_int W64.to_uint).
          exact W64.to_uintK.
          move => a h9.
          rewrite to_uint_small.
          have supp : 0 <= a <= 18446744073709551615.
          + by apply supp_dinter.
          smt().
          reflexivity.
          rewrite to_uint_small.
          have supp : 0 <= vR <= 18446744073709551615.
          + by apply supp_dinter.
          smt().
          by simplify.
        + move => vR tmp2L h8.
          split.
          + rewrite supp_dinter.    
            have eq : 0 <= to_uint tmp2L && to_uint tmp2L < W64.modulus.
            * apply W64.to_uint_cmp.
            smt.
          + move => h9.
            rewrite /EqWordInt in h2.
            by rewrite ultE h2.
              skip.
              move => &m1 &m2 /> h1 h2 h3 h4 h5 h6.
              rewrite /EqWordInt in h4.
              rewrite /EqWordInt in h5.
              do! split.
              + by rewrite ultE h4 h5.
              + by rewrite ultE h4 h5.
              + smt.
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

lemma imp_ref_rcg_equiv _set :
  equiv[M.random_char_generator ~ RPGRef.random_char_generator :
          _set = set{2} /\
          EqWordIntSet set{1} set{2} /\
          EqWordInt range{1} (size set{2}) /\
          0 < to_uint range{1} < W64.modulus
           ==>
          EqWordChar res{1} res{2} /\
          res{2} \in _set].
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
split.
- apply h1.
  by apply mem_range.
- apply mem_nth.
  split. assumption. move => h8. assumption.
qed.

lemma n_range_0 (n:int) :
  n \in range 0 0 => false.
proof.
smt(@List).
qed.

(*-------------------------------------*)
(*----- Def. UnionSet Equivalence -----*)
(*-------------------------------------*)

lemma imp_ref_define_union_set_equiv _nLowercase _nUppercase _nNumbers _nSpecial :
  equiv[M.define_union_set ~ RPGRef.define_union_set :
        nLowercase{2} = _nLowercase /\
        nUppercase{2} = _nUppercase /\
        nNumbers{2} = _nNumbers /\
        nSpecial{2} = _nSpecial /\
        EqWordInt lowercase_max{1} nLowercase{2} /\
        EqWordInt uppercase_max{1} nUppercase{2} /\
        EqWordInt numbers_max{1} nNumbers{2} /\
        EqWordInt special_max{1} nSpecial{2} /\
        EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
        EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
        EqWordIntSet numbers_set{1} numbersSet{2} /\
        EqWordIntSet special_set{1} specialSet{2} /\
        lowercaseSet{2} = lowercaseSet /\
        uppercaseSet{2} = uppercaseSet /\
        numbersSet{2} = numbersSet /\
        specialSet{2} = specialSet /\
        size lowercaseSet{2} = 26 /\
        size uppercaseSet{2} = 26 /\
        size numbersSet{2} = 10 /\
        size specialSet{2} = 14
         ==>
        to_uint res{1}.`1 = size res{2} /\
        EqWordIntSet res{1}.`2 res{2} /\
        (forall x, x \in res{2} =>
         x \in lowercaseSet{2} \/
         x \in uppercaseSet{2} \/
         x \in numbersSet{2} \/
         x \in specialSet{2}) /\
        (has (fun (x) => x \in res{2}) lowercaseSet{2} => 0 < _nLowercase) /\
        (has (fun (x) => x \in res{2}) uppercaseSet{2} => 0 < _nUppercase) /\
        (has (fun (x) => x \in res{2}) numbersSet{2} => 0 < _nNumbers) /\
        (has (fun (x) => x \in res{2}) specialSet{2} => 0 < _nSpecial)].
proof.
proc.
seq 1 1 : (#pre /\
           i_set{1} = W64.zero /\
           to_uint i_set{1} = size unionSet{2} /\
           EqWordIntSet union_set{1} unionSet{2}).
- auto.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 n h14.
  rewrite /= in h14.
  by apply n_range_0 in h14.

seq 1 1 : (nLowercase{2} = _nLowercase /\
           nUppercase{2} = _nUppercase /\
           nNumbers{2} = _nNumbers /\
           nSpecial{2} = _nSpecial /\
           EqWordInt lowercase_max{1} nLowercase{2} /\
           EqWordInt uppercase_max{1} nUppercase{2} /\
           EqWordInt numbers_max{1} nNumbers{2} /\
           EqWordInt special_max{1} nSpecial{2} /\
           EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} numbersSet{2} /\
           EqWordIntSet special_set{1} specialSet{2} /\
           lowercaseSet{2} = lowercaseSet /\
           uppercaseSet{2} = uppercaseSet /\
           numbersSet{2} = numbersSet /\
           specialSet{2} = specialSet /\
           size lowercaseSet{2} = 26 /\
           size uppercaseSet{2} = 26 /\
           size numbersSet{2} = 10 /\
           size specialSet{2} = 14 /\
           to_uint i_set{1} = size unionSet{2} /\
           EqWordIntSet union_set{1} unionSet{2} /\
           0 <= size unionSet{2} <= 26 /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2}) /\
           (has (mem unionSet{2}) lowercaseSet => 0 < _nLowercase)).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14.
    by rewrite -h1 ultE.
  + auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15.
    rewrite ultE /= in h15.
    rewrite /EqWOrdInt in h1.
    do! split.
    - by rewrite size_cat -h13 /= eq_sym.
    - rewrite /EqWordIntSet size_cat -h13 /=.
      rewrite /EqWordIntSet in h5.
      move => n.
      rewrite mem_range.
      move => [h16 h17].
      do! rewrite get_set_if /=.
      - case (n=25). move => h18.
        rewrite eq_sym size_eq0 in h13.
        rewrite h13 h18 /=.
        apply h5.
        rewrite mem_range /#.
        admit.
    - by rewrite size_cat h9 -h13.
    - by rewrite size_cat h9 -h13.
    - rewrite eq_sym size_eq0 in h13.
      by rewrite h13.
    - rewrite eq_sym size_eq0 in h13.
      rewrite h13 /=.
      rewrite charset_has /#.
  + auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15.
    rewrite eq_sym size_eq0 in h13.
    do! split.
    - smt().
    - smt().
    - move => x.
      by rewrite h13 /=.
    - rewrite h13.
      trivial.

seq 1 1 : (nLowercase{2} = _nLowercase /\
           nUppercase{2} = _nUppercase /\
           nNumbers{2} = _nNumbers /\
           nSpecial{2} = _nSpecial /\
           EqWordInt lowercase_max{1} nLowercase{2} /\
           EqWordInt uppercase_max{1} nUppercase{2} /\
           EqWordInt numbers_max{1} nNumbers{2} /\
           EqWordInt special_max{1} nSpecial{2} /\
           EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} numbersSet{2} /\
           EqWordIntSet special_set{1} specialSet{2} /\
           lowercaseSet{2} = lowercaseSet /\
           uppercaseSet{2} = uppercaseSet /\
           numbersSet{2} = numbersSet /\
           specialSet{2} = specialSet /\
           size lowercaseSet{2} = 26 /\
           size uppercaseSet{2} = 26 /\
           size numbersSet{2} = 10 /\
           size specialSet{2} = 14 /\
           to_uint i_set{1} = size unionSet{2} /\
           EqWordIntSet union_set{1} unionSet{2} /\
           0 <= size unionSet{2} <= 26 + 26 /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2} \/
            x \in uppercaseSet{2}) /\
           (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < _nLowercase) /\
           (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < _nUppercase)).
- if. 
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18.
    by rewrite -h2 ultE.
  + auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19.
    do! split.
    - rewrite size_cat -h13 h10 eq_sym to_uintD /=.
      have h20 : (to_uint i_set{m1} + 26) %% 18446744073709551616 =
                 (to_uint i_set{m1} + 26).
      + smt().
      by rewrite h20.
    - rewrite /EqWordIntSet size_cat -h13 /=.
      rewrite /EqWordIntSet in h6.
      move => n.
      rewrite mem_range.
      move => [h20 h21].
      do! rewrite get_set_if /=.
      + case (n = (to_uint i_set{m1}) + 25).
        move => h22.
        rewrite h22 /=.
        have : (0 <= to_uint (i_set{m1} + (of_int 25)%W64) &&
               to_uint (i_set{m1} + (of_int 25)%W64) < 76) /\
               to_uint i_set{m1} + 25 = to_uint (i_set{m1} + (of_int 25)%W64).
        + do! split.
          * rewrite to_uintD /= /#.
          * rewrite to_uintD h13 /#.
          * rewrite to_uintD /#.
        move => h23. rewrite h23 /=.
        rewrite nth_cat h13. have h24 : !(size unionSet{m2} + 25 < size unionSet{m2}). smt().
        rewrite h24 /=.
        have h25 : size unionSet{m2} + 25 - size unionSet{m2} = 25. smt().
        rewrite h25.
        apply h6.
        rewrite mem_range /#.
      + admit.
    - rewrite size_cat /#.
    - rewrite size_cat /#.
    - move => x h20.
      rewrite char_cat2 in h20.
      case h20.
      * move => h20.
        by rewrite h17.
      * move => h21.
        by rewrite h21.
    - move => h20.
      have disjoint : (forall (x : char), x \in lowercaseSet => ! (x \in uppercaseSet)).
      + rewrite /lowercaseSet /uppercaseSet /#.
    - have h21 : has (mem unionSet{m2}) lowercaseSet.
      + by apply (has_cat_set unionSet{m2} uppercaseSet lowercaseSet).
      by apply h18 in h21.
    - rewrite ultE /= in h19.
      by rewrite -h2.
  + auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19.
    do! split.
    - smt().
    - smt().
    - have disjoint : (forall (x : char), x \in lowercaseSet => ! (x \in uppercaseSet)).
      + rewrite /lowercaseSet /uppercaseSet /#.
      have : !(has (mem unionSet{m2}) uppercaseSet).
      + rewrite hasPn.
        move => x h20.
        rewrite disjoint_symmetry in disjoint.
        apply disjoint in h20.
        apply in_contra in h17.
        by apply h17 in h20.
      trivial.

seq 1 1 : (nLowercase{2} = _nLowercase /\
           nUppercase{2} = _nUppercase /\
           nNumbers{2} = _nNumbers /\
           nSpecial{2} = _nSpecial /\
           EqWordInt lowercase_max{1} nLowercase{2} /\
           EqWordInt uppercase_max{1} nUppercase{2} /\
           EqWordInt numbers_max{1} nNumbers{2} /\
           EqWordInt special_max{1} nSpecial{2} /\
           EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} numbersSet{2} /\
           EqWordIntSet special_set{1} specialSet{2} /\
           lowercaseSet{2} = lowercaseSet /\
           uppercaseSet{2} = uppercaseSet /\
           numbersSet{2} = numbersSet /\
           specialSet{2} = specialSet /\
           size lowercaseSet{2} = 26 /\
           size uppercaseSet{2} = 26 /\
           size numbersSet{2} = 10 /\
           size specialSet{2} = 14 /\
           to_uint i_set{1} = size unionSet{2} /\
           EqWordIntSet union_set{1} unionSet{2} /\
           0 <= size unionSet{2} <= 26 + 26 + 10 /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2} \/
            x \in uppercaseSet{2} \/
            x \in numbersSet{2}) /\
           (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < _nLowercase) /\
           (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < _nUppercase) /\
           (has (fun (x) => x \in unionSet{2}) numbersSet{2} => 0 < _nNumbers)).
- if.
  + admit.
  + admit.
  + admit.


seq 1 1 : (nLowercase{2} = _nLowercase /\
           nUppercase{2} = _nUppercase /\
           nNumbers{2} = _nNumbers /\
           nSpecial{2} = _nSpecial /\
           EqWordInt lowercase_max{1} nLowercase{2} /\
           EqWordInt uppercase_max{1} nUppercase{2} /\
           EqWordInt numbers_max{1} nNumbers{2} /\
           EqWordInt special_max{1} nSpecial{2} /\
           EqWordIntSet lowercase_set{1} lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} numbersSet{2} /\
           EqWordIntSet special_set{1} specialSet{2} /\
           lowercaseSet{2} = lowercaseSet /\
           uppercaseSet{2} = uppercaseSet /\
           numbersSet{2} = numbersSet /\
           specialSet{2} = specialSet /\
           size lowercaseSet{2} = 26 /\
           size uppercaseSet{2} = 26 /\
           size numbersSet{2} = 10 /\
           size specialSet{2} = 14 /\
           to_uint i_set{1} = size unionSet{2} /\
           EqWordIntSet union_set{1} unionSet{2} /\
           0 <= size unionSet{2} <= 26 + 26 + 10 + 14 /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2} \/
            x \in uppercaseSet{2} \/
            x \in numbersSet{2} \/
            x \in specialSet{2}) /\
           (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < _nLowercase) /\
           (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < _nUppercase) /\
           (has (fun (x) => x \in unionSet{2}) numbersSet{2} => 0 < _nNumbers) /\
           (has (fun (x) => x \in unionSet{2}) specialSet{2} => 0 < _nSpecial)).
- if.
  + admit.
  + admit.
  + admit.


auto.
qed.


(*-----------------------------*)
(*----- Perm. Equivalence -----*)
(*-----------------------------*)

lemma imp_ref_perm_equiv _addr _pw:
  equiv[M.permutation ~ RPGRef.permutation :
        _addr = W64.of_int 1000 /\
        p_string{1} = _addr /\
        pw{2} = _pw /\
        EqWordInt string_len{1} (size _pw) /\
        0 < size _pw <= 200 /\
        memPassword_eq_specPassword Glob.mem{1}  _addr _pw
        ==>
        memPassword_eq_specPassword Glob.mem{1} _addr res{2}].
proof.
proc.
seq 1 1 : (#pre /\ EqWordInt i{1} i{2} /\ i{2} = size pw{2}).
- auto.
while (_addr = W64.of_int 1000 /\
       p_string{1} = _addr /\
       EqWordInt string_len{1} (size _pw) /\
       EqWordInt i{1} i{2} /\
       size pw{2} <= 200 /\
       to_uint i{1} <= size pw{2} /\
       memPassword_eq_specPassword Glob.mem{1} _addr pw{2}).
+ seq 1 1 : (#pre /\ EqWordInt j{1} j{2}).
  - ecall (imp_ref_rng_equiv i{2}).
    skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7.
    split.
    * rewrite /EqWordInt in h2.
      by rewrite h2.
    * smt().
  seq 1 1 : (_addr = W64.of_int 1000 /\
             p_string{1} = _addr /\
             EqWordInt string_len{1} (size _pw) /\
             EqWordInt i{1} i{2} /\
             size pw{2} <= 200 /\
             to_uint i{1} < size pw{2} /\
             memPassword_eq_specPassword Glob.mem{1} _addr pw{2} /\
             W64.zero \ule i{1} /\
             0 <= i{2} /\
             EqWordInt j{1} j{2}).
  - auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8.
    rewrite /EqWordInt in h2.
    have h9 : W64.one \ule i{m1}.
    + rewrite uleE /= /#.
    do! split.
    - rewrite /EqWordInt to_uintB. assumption.
      by rewrite h2.
    - rewrite to_uintB. assumption.
      smt().
    - rewrite uleE to_uintB. assumption.
      rewrite h2 /#.
    - smt().
  seq 1 1 : (#pre /\ EqWordChar aux{1} aux{2}).
  - auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8.
    rewrite /EqWordInt in h2.
    rewrite /memPassword_eq_specPassword in h5.
    rewrite /EqWordChar.
    rewrite (nth_change_dfl (-1) 0).
    split. assumption. move => h9. by rewrite -h2.
    have h9 : i{m2} \in range 0 (size pw{m2}).
    + apply mem_range.
      split. assumption. move => h9. by rewrite -h2.
    rewrite h5. assumption.
    rewrite to_uintD_small.
    rewrite /EqWordInt in h1.
    smt().
    by rewrite h2.
  seq 1 1 : (#pre).
  - auto.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9.
    rewrite /EqWordInt in h2.
    rewrite /memPassword_eq_specPassword in h5.
    do! split.
    - by rewrite -(size_update ((nth 0 pw{m2} j{m2})) pw{m2} i{m2}).
    - by rewrite -(size_update ((nth 0 pw{m2} j{m2})) pw{m2} i{m2}).
    - rewrite /memPassword_eq_specPassword.
      move => n h10.
      rewrite -(size_update ((nth 0 pw{m2} j{m2})) pw{m2} i{m2}) in h10.
      rewrite to_uintD_small. smt().
      rewrite to_uintD_small /=. admit.
      admit.
  seq 1 1 : (#pre).
  - auto.    
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9.
     rewrite /EqWordInt in h2.
     rewrite /memPassword_eq_specPassword in h5.
     do! split.
     - by rewrite -(size_update aux{m2} pw{m2} j{m2}).
     - by rewrite -(size_update aux{m2} pw{m2} j{m2}).
     - rewrite /memPassword_eq_specPassword.
       move => n h10.
       rewrite -(size_update aux{m2} pw{m2} j{m2}) in h10.
       rewrite to_uintD_small /=. admit.
       admit.
auto.
move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9.
do! split.
rewrite /EqWordInt in h2.
- smt().
- by rewrite ultE h2.
- by rewrite ultE h2.
auto.
move => &m1 &m2 /> h1 h2 h3 h4 h5.
rewrite /EqWordInt in h5.
do! split.
- by rewrite h5.
- by rewrite ultE h5.
qed.




(*---------------------------*)
(*----- RPG Equivalence -----*)
(*---------------------------*)

(*OTHER POSSIBLE FORMALIZATION:
lemma implementation_reference_equiv :
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
case (25<n). rewrite mem_range /= in h1. smt().
rewrite mem_range /= in h1. smt().
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
    move => &m1 /> ??????????????????????????????????????????h1 h2.
    rewrite uleE /= in h1.
    rewrite ultE /= in h2.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      by simplify.
    - rewrite uleE to_uintD /=. smt().
    - rewrite to_uintD /=. smt().
  * skip.
    move => &m1 &m2 /> ??????????????????????????????????????????????h1.
    rewrite ultE ltrNge /= /#.
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
case (25<n). rewrite mem_range /= in h1. smt().
rewrite mem_range /= in h1. smt().
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
    move => &m1 /> ???????????????????????????????????????????h1 h2.
    rewrite uleE /= in h1.
    rewrite ultE /= in h2.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      by simplify.
    - rewrite uleE to_uintD /=. smt().
    - rewrite to_uintD /=. smt().
  * skip.
    move => &m1 &m2 /> ??????????????????????????????????????????????h1.
    rewrite ultE ltrNge /= /#.
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
case (9<n). rewrite mem_range /= in h1. smt().
rewrite mem_range /= in h1. smt().
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
    move => &m1 /> ????????????????????????????????????????????h1 h2.
    rewrite uleE /= in h1.
    rewrite ultE /= in h2.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      by simplify.
    - rewrite uleE to_uintD /=. smt().
    - rewrite to_uintD /=. smt().
  * skip.
    move => &m1 &m2 /> ??????????????????????????????????????????????h1.
    rewrite ultE ltrNge /= /#.
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
case (13<n). rewrite mem_range /= in h1. smt().
rewrite mem_range /= in h1. smt().
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
    move => &m1 /> ?????????????????????????????????????????????h1 h2.
    rewrite uleE /= in h1.
    rewrite ultE /= in h2.
    do! split.
    - apply append_trash_to_eq_set.
      assumption.
      by simplify.
    - rewrite uleE to_uintD /=. smt().
    - rewrite to_uintD /=. smt().
  * skip.
    move => &m1 &m2 /> ??????????????????????????????????????????????h1.
    rewrite ultE ltrNge /= /#.
seq 2 0 : (#pre).
- sp.
  while{1} (true) (76 - to_uint i{1}).
  * move => _ z.
    auto.
    move => &m /> h1.
    rewrite ultE /= in h1.
    rewrite to_uintD /=. smt().
  * skip.
    move => &m1 &m2 /> *.
    rewrite ultE ltrNge /= /#.
seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           specPolicy_eq_registers policy{2} length{1} lowercase_min{1}
             lowercase_max{1} uppercase_min{1} uppercase_max{1}
             numbers_min{1} numbers_max{1} special_min{1} special_max{1} /\
           0 < to_uint length{1} <= 200 /\
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
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
           i_filled{1} = W64.zero /\
           0 <= to_uint i_filled{1}).
- auto.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
          h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38
          h39 h40 h41 h42 h43 h44 h45.
  do! split.
  - smt().
  - smt().
  - smt().
  - smt().
  - smt().
  - smt().
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
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
           0 <= to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
            h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38
            h39 h40 h41 h42 h43 h44.
    split.
    * by rewrite ultE h41 /=.
    * by rewrite ultE h41 /=.
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
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
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
           EqWordInt i{1} i{2} /\
           lowercase_min{1} \ule i{1} + lowercase_max{1} /\
           0 <= to_uint i{1} <= to_uint lowercase_min{1} /\
           0 <= to_uint i_filled{1} /\
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
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
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
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 lowercase_min{1} \ule i{1} + lowercase_max{1} + W64.one /\
                 0 <= to_uint i{1} < to_uint lowercase_min{1} /\
                 i{1} = i_filled{1}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40 h41 h42 h43.
        rewrite uleE /= in h17.
        rewrite uleE /= in h18.
        rewrite ultE /= in h42.
        have h44 : 0 <= to_uint lowercase_max{m1} < W64.modulus.
        + apply W64.to_uint_cmp.
        rewrite uleE to_uintD in h38.
        do! split.
        - rewrite uleE to_uintB /=. rewrite uleE /=. smt().
          smt().
        - rewrite /EqWordInt to_uintB.
          rewrite uleE /=. smt().
          by rewrite h31.
        - rewrite uleE to_uintD to_uintD to_uintB /=.
          rewrite uleE /=. smt().
          have small1 : (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1)) %%
                          18446744073709551616 =
                        (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1)).
          + smt().
          rewrite small1.
          have small2 : (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1) + 1) %%
                          18446744073709551616 =
                        (to_uint i_filled{m1} + (to_uint lowercase_max{m1} - 1) + 1).
          + smt().
          rewrite small2.
          smt().
        - assumption.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - ecall (imp_ref_rcg_equiv lowercaseSet{2}).
        skip.
        move => &m1 &m2 /> *.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
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
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 lowercase_min{1} \ule i{1} + lowercase_max{1} /\
                 0 <= to_uint i{1} <= to_uint lowercase_min{1} /\
                 i{1} = i_filled{1} /\
                 0 <= to_uint i_filled{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40 h41.
        have i_filled_small : to_uint i_filled{m1} < 200.
        + rewrite uleE /= in h17. smt().
        do! split.
        - have small : (to_uint i_filled{m1} + 1) %% W64.modulus =
                       to_uint i_filled{m1} + 1.
          + smt().
          by rewrite to_uintD /= small -h35 size_cat /=.
        - rewrite to_uintD.
          have small : (1000 + to_uint i_filled{m1}) %% W64.modulus =
                       1000 + to_uint i_filled{m1}.
          + smt().
          rewrite small -h35 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - rewrite /EqWordInt in h37.
          rewrite /EqWordInt to_uintD_small /=.
          smt().
          by rewrite h37.
        - have h42 : i_filled{m1} + W64.one + lowercase_max{m1} =
                 i_filled{m1} + lowercase_max{m1} + W64.one.
          + ring.
          by rewrite h42.
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - rewrite to_uintD /= /#.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
              h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              h37 h38 h39 h40 h41 h42.
      do! split.
      - smt().
      - smt().
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
               h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
               h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47.
       rewrite /EqWordInt in h46.
       do! split.
       - smt().
       - rewrite h46.
         by rewrite uleE /= in h24.
       - by rewrite -to_uintK h46.
       - move => h48.
         rewrite -h14.
         rewrite ultE in h48.
         by rewrite h46 in h48.
       - move => h48.
         rewrite -h14 in h48.
         rewrite -h46 in h48.
         by rewrite ultE.
       - move => ? fL ? ? ? ? h48 ? ? ? ? ? ? ? ? h49.
         rewrite ultE ltrNge /= in h48.
         have h50 : to_uint fL <= to_uint lowercase_min{m1} &&
                    to_uint lowercase_min{m1} <= to_uint fL.
         + smt().
         apply ler_asym in h50.
         by rewrite to_uint_eq.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
            h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38
            h39 h40 h41 h42 h43 h44 h45.
     have : lowercase_min{m1} = W64.zero. 
    + rewrite ultE ltrNge /= in h45.
      rewrite uleE /= in h24.
      rewrite uleE /= in h27.
      have h46 : to_uint lowercase_min{m1} <= 0 && 0 <= to_uint lowercase_min{m1}.
      + have : to_uint lowercase_min{m1} <= 0.
        + apply (ler_trans (to_uint lowercase_max{m1}) (to_uint lowercase_min{m1}) 0).
          assumption.
          assumption.
        smt().
      rewrite to_uint_eq.
      by apply (ler_asym (to_uint lowercase_min{m1}) 0).
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
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
           0 <= to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
            h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37.
    split.
    * by rewrite ultE h32 /=.
    * by rewrite ultE h32 /=.
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
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
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
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
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
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
                 i_filled{1} = lowercase_min{1} + i{1} /\
                 0 <= to_uint i_filled{1}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40 h41.
        rewrite uleE /= in h20.
        rewrite uleE /= in h21.
        rewrite ultE /= in h40.
        have h43 : 0 <= to_uint uppercase_max{m1} < W64.modulus.
        + apply W64.to_uint_cmp.
        rewrite uleE to_uintD in h37.
        do! split.
        - rewrite uleE to_uintB /=. rewrite uleE /=. smt().
          smt().
        - rewrite /EqWordInt to_uintB.
          rewrite uleE /=. smt().
          by rewrite h31.
        - rewrite uleE to_uintD to_uintD to_uintB /=.
          rewrite uleE /=. smt().
          have small1 : (to_uint i{m1} + (to_uint uppercase_max{m1} - 1)) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint uppercase_max{m1} - 1)).
          + smt().
          rewrite small1.
          have small2 : (to_uint i{m1} + (to_uint uppercase_max{m1} - 1) + 1) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint uppercase_max{m1} - 1) + 1).
          + smt().
          rewrite small2.
          smt().
        - assumption.
        - rewrite to_uintD /= /#.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - ecall (imp_ref_rcg_equiv uppercaseSet{2}).
        skip.
        move => &m1 &m2 /> *.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
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
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 uppercase_min{1} \ule i{1} + uppercase_max{1} /\
                 0 <= to_uint i{1} <= to_uint uppercase_min{1} /\
                 i_filled{1} = lowercase_min{1} + i{1} /\
                 0 <= to_uint i_filled{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40 h41.
        have lowercase_min_small : to_uint lowercase_min{m1} <= 200.
        + by rewrite uleE in h17.
        have i_small : to_uint i{m1} < 200.
        + rewrite uleE /= in h20. smt().
        do! split.
        - rewrite to_uintD_small to_uintD_small. smt(). smt(). smt().
          rewrite size_cat /= h34 to_uintD_small. smt().
          reflexivity.
        - rewrite to_uintD.
          have small : (1000 + to_uint (lowercase_min{m1} + i{m1})) %% W64.modulus =
                       1000 + to_uint (lowercase_min{m1} + i{m1}).
          + rewrite to_uintD_small. smt().
            rewrite uleE /= in h16.
            rewrite uleE /= in h17.
            rewrite pmod_small.
            split. smt(). smt().
            reflexivity.
          rewrite small -h34 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - rewrite /EqWordInt in h36.
          rewrite /EqWordInt to_uintD_small /=.
          smt().
          by rewrite h36.
        - have h42 : i{m1} + W64.one + uppercase_max{m1} =
                     i{m1} + uppercase_max{m1} + W64.one.
          + ring.
          by rewrite h42.
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - ring.
        - rewrite to_uintD /= /#.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
              h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              h37 h38 h39 h40 h41.
      do! split.
      - smt().
      - smt().
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
               h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
               h37 h38 h39 h40.
       do! split.
       - smt().
       - rewrite /EqWordInt in h39.
         rewrite h39.
         by rewrite uleE /= in h19.
       - apply wordint_to_intword in h39.
         by rewrite -h39.
       - move => h41.
         rewrite -h2.
         rewrite ultE in h41.
         by rewrite h39 in h41.
       - move => h41.
         rewrite -h2 in h41.
         rewrite -h39 in h41.
         by rewrite ultE.
       - move => ? fL ? ? ? ? h41 ? ? ? ? ? ? ? ? h42.
         split.
         * rewrite ultE ltrNge /= in h41.
           have h43 : to_uint fL <= to_uint uppercase_min{m1} &&
                      to_uint uppercase_min{m1} <= to_uint fL.
           + smt().
           apply ler_asym in h43.
           rewrite -to_uint_eq in h43.
           by rewrite h43.
         * rewrite to_uintD /= /#.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
            h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38.
    have : uppercase_min{m1} = W64.zero.
    + rewrite ultE ltrNge /= in h38.
      rewrite uleE /= in h19.
      rewrite uleE /= in h22.
      have h39 : to_uint uppercase_min{m1} <= 0 && 0 <= to_uint uppercase_min{m1}.
      + have : to_uint uppercase_min{m1} <= 0.
        + apply (ler_trans (to_uint uppercase_max{m1}) (to_uint uppercase_min{m1}) 0).
          assumption.
          assumption.
        move => h40. split. assumption. move => h39. assumption.
      rewrite to_uint_eq.
      by apply (ler_asym (to_uint uppercase_min{m1}) 0).
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           i_filled{1} = lowercase_min{1} + uppercase_min{1} + numbers_min{1} /\
           0 <= to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
            h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36.
    split.
    * by rewrite ultE h32 /=.
    * by rewrite ultE h32 /=.
  + seq 1 1 : (#[/:]pre /\ 
               EqWordInt i{1} i{2} /\
               i{2} = 0 /\
               numbers_min{1} \ule i{1} + numbers_max{1}).
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           special_min{1} \ule special_max{1} /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
           EqWordInt i{1} i{2} /\
           numbers_min{1} \ule i{1} + numbers_max{1} /\
           0 <= to_uint i{1} <= to_uint numbers_min{1} /\
           i_filled{1} = lowercase_min{1} + uppercase_min{1} + i{1} /\
           0 <= to_uint i_filled{1}).
    * seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 numbers_min{1} \ule i{1} + numbers_max{1} + W64.one /\
                 0 <= to_uint i{1} < to_uint numbers_min{1} /\
                 i_filled{1} = lowercase_min{1} + uppercase_min{1} + i{1} /\
                 0 <= to_uint i_filled{1}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40 h41.
        rewrite uleE /= in h22.
        rewrite uleE /= in h23.
        rewrite uleE /= in h24.
        rewrite ultE /= in h40.
        have h42 : 0 <= to_uint numbers_max{m1} < W64.modulus.
        + apply W64.to_uint_cmp.
        rewrite uleE to_uintD in h36.
        do! split.
        - rewrite uleE to_uintB /=. rewrite uleE /=. smt().
          smt().
        - rewrite /EqWordInt to_uintB.
          rewrite uleE /=. smt().
          by rewrite h31.
        - rewrite uleE to_uintD to_uintD to_uintB /=.
          rewrite uleE /=. smt().
          have small1 : (to_uint i{m1} + (to_uint numbers_max{m1} - 1)) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint numbers_max{m1} - 1)).
          + smt().
          rewrite small1.
          have small2 : (to_uint i{m1} + (to_uint numbers_max{m1} - 1) + 1) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint numbers_max{m1} - 1) + 1).
          + smt().
          rewrite small2.
          smt().
        - assumption.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - ecall (imp_ref_rcg_equiv numbersSet{2}).
        skip.
        move => &m1 &m2 /> *.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 special_min{1} \ule special_max{1} /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 numbers_min{1} \ule i{1} + numbers_max{1} /\
                 0 <= to_uint i{1} <= to_uint numbers_min{1} /\
                 i_filled{1} = lowercase_min{1} + uppercase_min{1} + i{1} /\
                 0 <= to_uint i_filled{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40.
        have lowercase_min_small : to_uint lowercase_min{m1} <= 200.
        + by rewrite uleE in h17.
        have uppercase_min_small : to_uint uppercase_min{m1} <= 200.
        + by rewrite uleE in h20.
        have i_small : to_uint i{m1} < 200.
        + rewrite uleE /= in h23. smt().
        do! split.
        - rewrite to_uintD_small to_uintD_small to_uintD_small.
          smt(). smt(). smt(). smt(). smt(). smt(). smt().
          rewrite size_cat /= h33 to_uintD_small to_uintD_small. smt(). smt(). smt().
          reflexivity.
        - rewrite to_uintD.
          have small :
              (1000 + to_uint (lowercase_min{m1} + uppercase_min{m1} + i{m1})) %% W64.modulus =
              1000 + to_uint (lowercase_min{m1} + uppercase_min{m1}  + i{m1}).
          + rewrite to_uintD_small to_uintD_small.
            smt(). smt(). smt().
            rewrite uleE /= in h16.
            rewrite uleE /= in h17.
            rewrite uleE /= in h19.
            rewrite uleE /= in h20.
            rewrite pmod_small.
            split. smt(). smt().
            reflexivity.
          rewrite small -h33 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - rewrite /EqWordInt in h35.
          rewrite /EqWordInt to_uintD_small /=.
          smt().
          by rewrite h35.
        - have h41 : i{m1} + W64.one + numbers_max{m1} =
                     i{m1} + numbers_max{m1} + W64.one.
          + ring.
          by rewrite h41.
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - ring.
        - rewrite to_uintD to_uintD to_uintD /= /#.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
              h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37
              h38 h39 h40.
      do! split.
      - smt().
      - smt().
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
               h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
               h37 h38 h39.
       do! split.
       - smt().
       - rewrite /EqWordInt in h38.
         rewrite h38.
         by rewrite uleE /= in h22.
       - apply wordint_to_intword in h38.
         by rewrite -to_uintK -h38.
       - move => h40.
         rewrite -h3.
         rewrite ultE in h40.
         by rewrite h38 in h40.
       - move => h40.
         rewrite -h3 in h40.
         rewrite -h38 in h40.
         by rewrite ultE.
       - move => ? fL ? ? ? ? h40 ? ? ? ? ? ? ? ? h41.
         rewrite ultE ltrNge /= in h40.
         have h42 : to_uint fL <= to_uint numbers_min{m1} &&
                    to_uint numbers_min{m1} <= to_uint fL.
         + smt().
         apply ler_asym in h42.
         rewrite -to_uint_eq in h42.
         by rewrite h42.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
            h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37.
    have : numbers_min{m1} = W64.zero.
    + rewrite ultE ltrNge /= in h37.
      rewrite uleE /= in h22.
      rewrite uleE /= in h25.
      have h38 : to_uint numbers_min{m1} <= 0 && 0 <= to_uint numbers_min{m1}.
      + have : to_uint numbers_min{m1} <= 0.
        + apply (ler_trans (to_uint numbers_max{m1}) (to_uint numbers_min{m1}) 0).
          assumption.
          assumption.
        move => h38. split. assumption. move => h39. assumption.
      rewrite to_uint_eq.
      by apply (ler_asym (to_uint numbers_min{m1}) 0).
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           i_filled{1} = lowercase_min{1} + uppercase_min{1} + numbers_min{1} + special_min{1}/\
           0 <= to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
- if.
  + move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
            h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35.
    split.
    * by rewrite ultE h32 /=.
    * by rewrite ultE h32 /=.
  + seq 1 1 : (#[/:]pre /\ 
               EqWordInt i{1} i{2} /\
               i{2} = 0 /\
               special_min{1} \ule i{1} + special_max{1}).
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
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`length /\
           0 < to_uint length{1} <= 200 /\
           W64.zero \ule lowercase_min{1} /\
           lowercase_min{1} \ule W64.of_int 200 /\
           lowercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule uppercase_min{1} /\
           uppercase_min{1} \ule W64.of_int 200 /\
           uppercase_max{1} \ule W64.of_int 200 /\
           W64.zero \ule numbers_min{1} /\
           numbers_min{1} \ule W64.of_int 200 /\
           numbers_max{1} \ule W64.of_int 200 /\
           W64.zero \ule special_min{1} /\
           special_min{1} \ule W64.of_int 200 /\
           special_max{1} \ule W64.of_int 200 /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           size generatedPassword{2} = W64.to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
           EqWordInt i{1} i{2} /\
           special_min{1} \ule i{1} + special_max{1} /\
           0 <= to_uint i{1} <= to_uint special_min{1} /\
           i_filled{1} = lowercase_min{1} + uppercase_min{1} + numbers_min{1} + i{1} /\
           0 <= to_uint i_filled{1}).
    * seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 special_min{1} \ule i{1} + special_max{1} + W64.one /\
                 0 <= to_uint i{1} < to_uint special_min{1} /\
                 i_filled{1} = lowercase_min{1} + uppercase_min{1} + numbers_min{1} + i{1} /\
                 0 <= to_uint i_filled{1}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39 h40.
        rewrite uleE /= in h25.
        rewrite uleE /= in h26.
        rewrite uleE /= in h27.
        rewrite ultE /= in h39.
        have h41 : 0 <= to_uint special_max{m1} < W64.modulus.
        + apply W64.to_uint_cmp.
        rewrite uleE to_uintD in h35.
        do! split.
        - rewrite uleE to_uintB /=. rewrite uleE /=. smt().
          smt().
        - rewrite /EqWordInt to_uintB.
          rewrite uleE /=. smt().
          by rewrite h31.
        - rewrite uleE to_uintD to_uintD to_uintB /=.
          rewrite uleE /=. smt().
          have small1 : (to_uint i{m1} + (to_uint special_max{m1} - 1)) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint special_max{m1} - 1)).
          + smt().
          rewrite small1.
          have small2 : (to_uint i{m1} + (to_uint special_max{m1} - 1) + 1) %%
                          18446744073709551616 =
                        (to_uint i{m1} + (to_uint special_max{m1} - 1) + 1).
          + smt().
          rewrite small2.
          smt().
        - assumption.
      seq 1 1 : (#pre /\ EqWordChar tmp8{1} randomChar{2}).
      - ecall (imp_ref_rcg_equiv specialSet{2}).
        skip.
        move => &m1 &m2 /> *.
      seq 3 2 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`length /\
                 0 < to_uint length{1} <= 200 /\
                 W64.zero \ule lowercase_min{1} /\
                 lowercase_min{1} \ule W64.of_int 200 /\
                 lowercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule uppercase_min{1} /\
                 uppercase_min{1} \ule W64.of_int 200 /\
                 uppercase_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule numbers_min{1} /\
                 numbers_min{1} \ule W64.of_int 200 /\
                 numbers_max{1} \ule W64.of_int 200 /\
                 W64.zero \ule special_min{1} /\
                 special_min{1} \ule W64.of_int 200 /\
                 special_max{1} \ule W64.of_int 200 /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 size generatedPassword{2} = W64.to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                   generatedPassword{2} /\
                 EqWordInt i{1} i{2} /\
                 special_min{1} \ule i{1} + special_max{1} /\
                 0 <= to_uint i{1} <= to_uint special_min{1} /\
                 i_filled{1} = lowercase_min{1} + uppercase_min{1} + numbers_min{1} + i{1} /\
                 0 <= to_uint i_filled{1} /\
                 EqWordChar tmp8{1} randomChar{2}).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
                h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                h37 h38 h39.
        have lowercase_min_small : to_uint lowercase_min{m1} <= 200.
        + by rewrite uleE in h17.
        have uppercase_min_small : to_uint uppercase_min{m1} <= 200.
        + by rewrite uleE in h20.
        have numbers_min_small : to_uint numbers_min{m1} <= 200.
        + by rewrite uleE in h23.
        have i_small : to_uint i{m1} < 200.
        + rewrite uleE /= in h26. smt().
        do! split.
        - rewrite to_uintD_small to_uintD_small to_uintD_small to_uintD_small.
          smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().
          smt(). smt(). smt(). smt().
          rewrite size_cat /= h32 to_uintD_small to_uintD_small to_uintD_small.
          smt(). smt(). smt(). smt(). smt(). smt(). smt().
          reflexivity.
        - rewrite to_uintD.
          have small :
              (1000 + to_uint (lowercase_min{m1} + uppercase_min{m1} + numbers_min{m1} + i{m1}))
              %% W64.modulus =
              1000 + to_uint (lowercase_min{m1} + uppercase_min{m1} + numbers_min{m1} + i{m1}).
          + rewrite to_uintD_small to_uintD_small to_uintD_small.
            smt(). smt(). smt(). smt(). smt(). smt(). smt().
            rewrite uleE /= in h16.
            rewrite uleE /= in h17.
            rewrite uleE /= in h19.
            rewrite uleE /= in h20.
            rewrite uleE /= in h22.
            rewrite uleE /= in h23.
            rewrite pmod_small.
            split. smt(). smt().
            reflexivity.
          rewrite small -h32 /=.
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
        - rewrite /EqWordInt in h34.
          rewrite /EqWordInt to_uintD_small /=.
          smt().
          by rewrite h34.
        - have h40 : i{m1} + W64.one + special_max{m1} =
                     i{m1} + special_max{m1} + W64.one.
          + ring.
          by rewrite h40.
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - rewrite to_uintD_small /=.
          smt().
          smt().
        - ring.
        - rewrite to_uintD to_uintD to_uintD to_uintD /= /#.
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
              h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
              h37 h38 h39.
      do! split.
      - smt().
      - smt().
    *  skip.
       move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
               h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38.
       do! split.
       - smt().
       - rewrite /EqWordInt in h37.
         rewrite h37.
         by rewrite uleE /= in h25.
       - apply wordint_to_intword in h37.
         by rewrite -to_uintK -h37.
       - move => h39.
         rewrite -h4.
         rewrite ultE in h39.
         by rewrite h37 in h39.
       - move => h39.
         rewrite -h4 in h39.
         rewrite -h37 in h39.
         by rewrite ultE.
       - move => ? fL ? ? ? ? h40 ? ? ? ? ? ? ? ? h41.
         rewrite ultE ltrNge /= in h40.
         have h42 : to_uint fL <= to_uint special_min{m1} &&
                    to_uint special_min{m1} <= to_uint fL.
         + smt().
         apply ler_asym in h42.
         rewrite -to_uint_eq in h42.
         by rewrite h42.
  + skip.
    move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
            h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36.
    have : special_min{m1} = W64.zero.
    + rewrite ultE ltrNge /= in h36.
      rewrite uleE /= in h25.
      rewrite uleE /= in h28.
      have h37 : to_uint special_min{m1} <= 0 && 0 <= to_uint special_min{m1}.
      + have : to_uint special_min{m1} <= 0.
        + apply (ler_trans (to_uint special_max{m1}) (to_uint special_min{m1}) 0).
          assumption.
          assumption.
        move => h37. split. assumption. move => h38. assumption.
      rewrite to_uint_eq.
      by apply (ler_asym (to_uint special_min{m1}) 0).
    trivial.

seq 1 1 : (#pre /\
           EqWordIntSet union_set{1} unionSet{2} /\
           to_uint tmp64_1{1} = size unionSet{2} /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2} \/
            x \in uppercaseSet{2} \/
            x \in numbersSet{2} \/
            x \in specialSet{2}) /\
           (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < lowercaseAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < uppercaseAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) numbersSet{2} => 0 < numbersAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) specialSet{2} => 0 < specialAvailable{2})).
ecall (imp_ref_define_union_set_equiv
       lowercaseAvailable{2} uppercaseAvailable{2} numbersAvailable{2} specialAvailable{2}).
auto.

(* JUST TO SIMPLIFY PROOFS! THIS SHOULD BE DONE EARLIER *)
seq 1 0 : (output_addr{1} = (W64.of_int 1000) /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           RPGRef.lowercaseSet{2} = lowercaseSet /\
           RPGRef.uppercaseSet{2} = uppercaseSet /\
           RPGRef.numbersSet{2} = numbersSet /\
           RPGRef.specialSet{2} = specialSet /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
           0 < to_uint length{1} <= 200 /\
           0 <= to_uint lowercase_min{1} /\
           to_uint lowercase_min{1} <= 200 /\
           to_uint lowercase_max{1} <= 200 /\
           0 <= to_uint uppercase_min{1} /\
           to_uint uppercase_min{1} <= 200 /\
           to_uint uppercase_max{1} <= 200 /\
           0 <= to_uint numbers_min{1} /\
           to_uint numbers_min{1} <= 200 /\
           to_uint numbers_max{1} <= 200 /\
           0 <= to_uint special_min{1} /\
           to_uint special_min{1} <= 200 /\
           to_uint special_max{1} <= 200 /\
           size generatedPassword{2} = to_uint i_filled{1} /\
           0 <= to_uint i_filled{1} /\
           i_filled{1} =
             lowercase_min{1} + uppercase_min{1} + numbers_min{1} + special_min{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
             generatedPassword{2} /\
           EqWordIntSet union_set{1} unionSet{2} /\
           to_uint tmp64_1{1} = size unionSet{2} /\
           (forall x, x \in unionSet{2} =>
            x \in lowercaseSet{2} \/
            x \in uppercaseSet{2} \/
            x \in numbersSet{2} \/
            x \in specialSet{2}) /\
           (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < lowercaseAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < uppercaseAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) numbersSet{2} => 0 < numbersAvailable{2}) /\
           (has (fun (x) => x \in unionSet{2}) specialSet{2} => 0 < specialAvailable{2}) /\
           EqWordInt tmp64_2{1} policy{2}.`PassCertRPG_ref.length).
auto.
move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
        h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41.
rewrite uleE in h16.
rewrite uleE in h17.
rewrite uleE in h18.
rewrite uleE in h19.
rewrite uleE in h20.
rewrite uleE in h21.
rewrite uleE in h22.
rewrite uleE in h23.
rewrite uleE in h24.
rewrite uleE in h25.
rewrite uleE in h26.
by rewrite uleE in h27.

seq 1 1 : (output_addr{1} = (W64.of_int 1000) /\
           to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
           to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
           to_uint numbers_min{1} = policy{2}.`numbersMin /\
           to_uint special_min{1} = policy{2}.`specialMin /\
           EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
           EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
           EqWordInt numbers_max{1} numbersAvailable{2} /\
           EqWordInt special_max{1} specialAvailable{2} /\
           EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
           EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
           EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
           EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
           size RPGRef.lowercaseSet{2} = 26 /\
           size RPGRef.uppercaseSet{2} = 26 /\
           size RPGRef.numbersSet{2} = 10 /\
           size RPGRef.specialSet{2} = 14 /\
           EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
           0 < to_uint length{1} <= 200 /\
           0 <= to_uint lowercase_min{1} /\
           to_uint lowercase_min{1} <= 200 /\
           to_uint lowercase_max{1} <= 200 /\
           0 <= to_uint uppercase_min{1} /\
           to_uint uppercase_min{1} <= 200 /\
           to_uint uppercase_max{1} <= 200 /\
           0 <= to_uint numbers_min{1} /\
           to_uint numbers_min{1} <= 200 /\
           to_uint numbers_max{1} <= 200 /\
           0 <= to_uint special_min{1} /\
           to_uint special_min{1} <= 200 /\
           to_uint special_max{1} <= 200 /\
           size generatedPassword{2} = to_uint i_filled{1} /\
           0 <= to_uint i_filled{1} /\
           memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000) generatedPassword{2}).
while (output_addr{1} = (W64.of_int 1000) /\
       to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
       to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
       to_uint numbers_min{1} = policy{2}.`numbersMin /\
       to_uint special_min{1} = policy{2}.`specialMin /\
       EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
       EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
       EqWordInt numbers_max{1} numbersAvailable{2} /\
       EqWordInt special_max{1} specialAvailable{2} /\
       EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
       EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
       EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
       EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
       RPGRef.lowercaseSet{2} = lowercaseSet /\
       RPGRef.uppercaseSet{2} = uppercaseSet /\
       RPGRef.numbersSet{2} = numbersSet /\
       RPGRef.specialSet{2} = specialSet /\
       size RPGRef.lowercaseSet{2} = 26 /\
       size RPGRef.uppercaseSet{2} = 26 /\
       size RPGRef.numbersSet{2} = 10 /\
       size RPGRef.specialSet{2} = 14 /\
       EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
       0 < to_uint length{1} <= 200 /\
       0 <= to_uint lowercase_min{1} /\
       to_uint lowercase_min{1} <= 200 /\
       to_uint lowercase_max{1} <= 200 /\
       0 <= to_uint uppercase_min{1} /\
       to_uint uppercase_min{1} <= 200 /\
       to_uint uppercase_max{1} <= 200 /\
       0 <= to_uint numbers_min{1} /\
       to_uint numbers_min{1} <= 200 /\
       to_uint numbers_max{1} <= 200 /\
       0 <= to_uint special_min{1} /\
       to_uint special_min{1} <= 200 /\
       to_uint special_max{1} <= 200 /\
       size generatedPassword{2} = to_uint i_filled{1} /\
       0 <= to_uint i_filled{1} /\
       memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
         generatedPassword{2} /\
       EqWordIntSet union_set{1} unionSet{2} /\
       to_uint tmp64_1{1} = size unionSet{2} /\
       (forall x, x \in unionSet{2} =>
        x \in lowercaseSet{2} \/
        x \in uppercaseSet{2} \/
        x \in numbersSet{2} \/
        x \in specialSet{2}) /\
       (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} => 0 < lowercaseAvailable{2}) /\
       (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} => 0 < uppercaseAvailable{2}) /\
       (has (fun (x) => x \in unionSet{2}) numbersSet{2} => 0 < numbersAvailable{2}) /\
       (has (fun (x) => x \in unionSet{2}) specialSet{2} => 0 < specialAvailable{2}) /\
       EqWordInt tmp64_2{1} policy{2}.`PassCertRPG_ref.length).
seq 1 1 : (#pre /\
           EqWordChar tmp8{1} randomChar{2} /\
           randomChar{2} \in unionSet{2}).
- ecall (imp_ref_rcg_equiv unionSet{2}).
  auto.
  move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18
          h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37
          h38 h39 h40 h41 h42 h43 h44.
  rewrite /EqWordInt in h1.
  rewrite h36.
  admit. (*size unionSet bounded*)
if{1}.
+ if.
  - move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
                       h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36
                       h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47.
    split.
    * move => h48.
      rewrite uleE /= in h47.
      rewrite uleE /= in h48.
      rewrite /EqWordChar in h45.
      rewrite -h45 /lowercaseSet /#.
    * move => h48.
      rewrite uleE /= in h47.
      rewrite /lowercaseSet in h48.
      rewrite /EqWordChar in h45.
      rewrite -h45 in h48.
      rewrite uleE /= /#. 
  - seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
               to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
               to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
               to_uint numbers_min{1} = policy{2}.`numbersMin /\
               to_uint special_min{1} = policy{2}.`specialMin /\
               EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
               EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
               EqWordInt numbers_max{1} numbersAvailable{2} /\
               EqWordInt special_max{1} specialAvailable{2} /\
               EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
               EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
               EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
               EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
               RPGRef.lowercaseSet{2} = lowercaseSet /\
               RPGRef.uppercaseSet{2} = uppercaseSet /\
               RPGRef.numbersSet{2} = numbersSet /\
               RPGRef.specialSet{2} = specialSet /\
               size RPGRef.lowercaseSet{2} = 26 /\
               size RPGRef.uppercaseSet{2} = 26 /\
               size RPGRef.numbersSet{2} = 10 /\
               size RPGRef.specialSet{2} = 14 /\
               EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
               (0 <  to_uint length{1} <= 200) /\
               0 <= to_uint lowercase_min{1} /\
               to_uint lowercase_min{1} <= 200 /\
               to_uint lowercase_max{1} <= 200 /\
               0 <= to_uint uppercase_min{1} /\
               to_uint uppercase_min{1} <= 200 /\
               to_uint uppercase_max{1} <= 200 /\
               0 <= to_uint numbers_min{1} /\
               to_uint numbers_min{1} <= 200 /\
               to_uint numbers_max{1} <= 200 /\
               0 <= to_uint special_min{1} /\
               to_uint special_min{1} <= 200 /\
               to_uint special_max{1} <= 200 /\
               size generatedPassword{2} = to_uint i_filled{1} /\
               0 <= to_uint i_filled{1} /\
               memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                 generatedPassword{2} /\
               EqWordIntSet union_set{1} unionSet{2} /\
               to_uint tmp64_1{1} = size unionSet{2} /\
               EqWordInt tmp64_2{1} policy{2}.`PassCertRPG_ref.length /\
               (i_filled{1} \ult tmp64_2{1}) /\
               size generatedPassword{2} < policy{2}.`PassCertRPG_ref.length /\
               EqWordChar tmp8{1} randomChar{2} /\
               (randomChar{2} \in unionSet{2}) /\
               (W8.of_int 97 \ule tmp8{1}) /\
               (tmp8{1} \ule W8.of_int 122)).
    + auto.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
              h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40
              h41 h42 h43 h44 h45 h46 h47 h48.
      have h49 : randomChar{m2} \in lowercaseSet.
      + rewrite uleE /= in h47.
        rewrite uleE /= in h48.
        rewrite /lowercaseSet.
        rewrite /EqWordChar in h45.
        rewrite -h45 /#.
      have h50 : 0 < lowercaseAvailable{m2}.
      + have h51 : has (mem unionSet{m2}) lowercaseSet{m2}.
        + by apply (charset_mem_has randomChar{m2} unionSet{m2} lowercaseSet{m2}).
        by apply h38 in h51.
      split.
      * rewrite /EqWordInt in h5.
        rewrite /EqWordInt to_uintB.
        rewrite uleE h5 /= /#.
        by rewrite h5.
      * rewrite to_uintB.
        rewrite uleE h5 /= /#.
        smt().
    if.
    * move => &m1 &m2 /> ????h1*.
      rewrite /EqWordInt -h1.
      by rewrite to_uint_eq /=.
    * seq 1 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
                 (0 < to_uint length{1} <= 200) /\
                 0 <= to_uint lowercase_min{1} /\
                 to_uint lowercase_min{1} <= 200 /\
                 to_uint lowercase_max{1} <= 200 /\
                 0 <= to_uint uppercase_min{1} /\
                 to_uint uppercase_min{1} <= 200 /\
                 to_uint uppercase_max{1} <= 200 /\
                 0 <= to_uint numbers_min{1} /\
                 to_uint numbers_min{1} <= 200 /\
                 to_uint numbers_max{1} <= 200 /\
                 0 <= to_uint special_min{1} /\
                 to_uint special_min{1} <= 200 /\
                 to_uint special_max{1} <= 200 /\
                 size generatedPassword{2} = to_uint i_filled{1} /\
                 0 <= to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                    generatedPassword{2} /\
                 EqWordIntSet union_set{1} unionSet{2} /\
                 to_uint tmp64_1{1} = size unionSet{2} /\
                 EqWordInt tmp64_2{1} policy{2}.`PassCertRPG_ref.length /\
                 (i_filled{1} \ult tmp64_2{1}) /\
                 size generatedPassword{2} < policy{2}.`PassCertRPG_ref.length /\
                 EqWordChar tmp8{1} randomChar{2} /\
                 (W8.of_int 97 \ule tmp8{1}) /\
                 (tmp8{1} \ule W8.of_int 122) /\
                 lowercase_max{1} = W64.zero /\
                 (forall x, x \in unionSet{2} =>
                  x \in lowercaseSet{2} \/
                  x \in uppercaseSet{2} \/
                  x \in numbersSet{2} \/
                  x \in specialSet{2}) /\
                 (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} =>
                    0 < lowercaseAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} =>
                    0 < uppercaseAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) numbersSet{2} =>
                    0 < numbersAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) specialSet{2} =>
                    0 < specialAvailable{2})).
       + ecall (imp_ref_define_union_set_equiv
         lowercaseAvailable{2} uppercaseAvailable{2} numbersAvailable{2} specialAvailable{2}).
         auto.
      seq 2 1 : (output_addr{1} = W64.of_int 1000 /\
                 to_uint lowercase_min{1} = policy{2}.`lowercaseMin /\
                 to_uint uppercase_min{1} = policy{2}.`uppercaseMin /\
                 to_uint numbers_min{1} = policy{2}.`numbersMin /\
                 to_uint special_min{1} = policy{2}.`specialMin /\
                 EqWordInt lowercase_max{1} lowercaseAvailable{2} /\
                 EqWordInt uppercase_max{1} uppercaseAvailable{2} /\
                 EqWordInt numbers_max{1} numbersAvailable{2} /\
                 EqWordInt special_max{1} specialAvailable{2} /\
                 EqWordIntSet lowercase_set{1} RPGRef.lowercaseSet{2} /\
                 EqWordIntSet uppercase_set{1} RPGRef.uppercaseSet{2} /\
                 EqWordIntSet numbers_set{1} RPGRef.numbersSet{2} /\
                 EqWordIntSet special_set{1} RPGRef.specialSet{2} /\
                 RPGRef.lowercaseSet{2} = lowercaseSet /\
                 RPGRef.uppercaseSet{2} = uppercaseSet /\
                 RPGRef.numbersSet{2} = numbersSet /\
                 RPGRef.specialSet{2} = specialSet /\
                 size RPGRef.lowercaseSet{2} = 26 /\
                 size RPGRef.uppercaseSet{2} = 26 /\
                 size RPGRef.numbersSet{2} = 10 /\
                 size RPGRef.specialSet{2} = 14 /\
                 EqWordInt length{1} policy{2}.`PassCertRPG_ref.length /\
                 (0 < to_uint length{1} <= 200) /\
                 0 <= to_uint lowercase_min{1} /\
                 to_uint lowercase_min{1} <= 200 /\
                 to_uint lowercase_max{1} <= 200 /\
                 0 <= to_uint uppercase_min{1} /\
                 to_uint uppercase_min{1} <= 200 /\
                 to_uint uppercase_max{1} <= 200 /\
                 0 <= to_uint numbers_min{1} /\
                 to_uint numbers_min{1} <= 200 /\
                 to_uint numbers_max{1} <= 200 /\
                 0 <= to_uint special_min{1} /\
                 to_uint special_min{1} <= 200 /\
                 to_uint special_max{1} <= 200 /\
                 size generatedPassword{2} = to_uint i_filled{1} /\
                 0 <= to_uint i_filled{1} /\
                 memPassword_eq_specPassword Glob.mem{1} (W64.of_int 1000)
                    generatedPassword{2} /\
                 EqWordIntSet union_set{1} unionSet{2} /\
                 to_uint tmp64_1{1} = size unionSet{2} /\
                 EqWordInt tmp64_2{1} policy{2}.`PassCertRPG_ref.length /\
                 EqWordChar tmp8{1} randomChar{2} /\
                 (W8.of_int 97 \ule tmp8{1}) /\
                 (tmp8{1} \ule W8.of_int 122) /\
                 lowercase_max{1} = W64.zero /\
                 (forall x, x \in unionSet{2} =>
                  x \in lowercaseSet{2} \/
                  x \in uppercaseSet{2} \/
                  x \in numbersSet{2} \/
                  x \in specialSet{2}) /\
                 (has (fun (x) => x \in unionSet{2}) lowercaseSet{2} =>
                    0 < lowercaseAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) uppercaseSet{2} =>
                    0 < uppercaseAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) numbersSet{2} =>
                    0 < numbersAvailable{2}) /\
                 (has (fun (x) => x \in unionSet{2}) specialSet{2} =>
                    0 < specialAvailable{2})).
      - auto.
        move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
                h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39
                h40 h41 h42 h43 h44 h45 h46.
        do! split.
        + rewrite size_cat to_uintD -h31 /= pmod_small.
          smt().
          reflexivity.
        + rewrite to_uintD /= /#.
        + rewrite to_uintD_small /= -h31.
          smt().                  
          by apply (eq_mem_password_append Glob.mem{m1}
          (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
      skip.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
              h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39
              h40 h41 h42 h43 h44.
      rewrite /EqWordInt in h36.
      by rewrite ultE h36 -h31.
    * auto.
      move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
              h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39
              h40 h41 h42 h43 h44.
      do! split.
      + rewrite size_cat to_uintD_small /=. smt(). by rewrite h32.
      + rewrite to_uintD /= /#.
      + rewrite to_uintD_small /= -h32.
        smt().                  
        by apply (eq_mem_password_append Glob.mem{m1}
        (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
      + rewrite ultE to_uintD_small /=. smt().
        rewrite /EqWordInt in h37.
        by rewrite -h32 size_cat /= h37.
      + rewrite ultE to_uintD_small /=. smt().
        rewrite /EqWordInt in h37.
        by rewrite -h32 size_cat /= h37.
  - if{2}.
    * conseq (_: false ==> _).
      - move => &m1 &m2 h1.
        have h2 : RPGRef.uppercaseSet{m2} = uppercaseSet by smt().
        have h3 : randomChar{m2} \in RPGRef.uppercaseSet{m2} by smt().
        rewrite h2 /uppercaseSet in h3.
        have h4 : 64 <= randomChar{m2} <= 90 by smt().
        have h5 : EqWordChar tmp8{m1} randomChar{m2} by smt().
        have h6 : !(tmp8{m1} \ule W8.of_int 122) by smt().
        rewrite /EqWordChar in h5.
        rewrite uleE lerNgt /= in h6.
        rewrite h5 in h6.
        smt().
      - trivial.
    * if{2}.
      * conseq (_: false ==> _).
        - move => &m1 &m2 h1.
          have h2 : RPGRef.numbersSet{m2} = numbersSet by smt().
          have h3 : randomChar{m2} \in RPGRef.numbersSet{m2} by smt().
          rewrite h2 /numbersSet in h3.
          have h4 : 48 <= randomChar{m2} <= 57 by smt().
          have h5 : EqWordChar tmp8{m1} randomChar{m2} by smt().
          have h6 : !(tmp8{m1} \ule W8.of_int 122) by smt().
          rewrite /EqWordChar in h5.
          rewrite uleE lerNgt /= in h6.
          rewrite h5 in h6.
          smt().
        - trivial.
      * if{2}.
        * conseq (_: false ==> _).
          - move => &m1 &m2 h1.
            have h2 : RPGRef.specialSet{m2} = specialSet by smt().
            have h3 : randomChar{m2} \in RPGRef.specialSet{m2} by smt().
            rewrite h2 /specialSet in h3.
            have h4 : randomChar{m2} = 33 \/
                      randomChar{m2} = 63 \/
                      randomChar{m2} = 35 \/
                      randomChar{m2} = 36 \/
                      randomChar{m2} = 37 \/
                      randomChar{m2} = 38 \/
                      randomChar{m2} = 43 \/
                      randomChar{m2} = 45 \/
                      randomChar{m2} = 42 \/
                      randomChar{m2} = 95 \/
                      randomChar{m2} = 64 \/
                      randomChar{m2} = 58 \/
                      randomChar{m2} = 59 \/
                      randomChar{m2} = 61 by smt().
            have h5 : EqWordChar tmp8{m1} randomChar{m2} by smt().
            have h6 : !(tmp8{m1} \ule W8.of_int 122) by smt().
            rewrite /EqWordChar in h5.
            rewrite uleE lerNgt /= in h6.
            rewrite h5 in h6.
            smt().
          - trivial.
        * auto.
          move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
                  h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38
                  h39 h40 h41 h42 h43 h44 h45 h46 h47 h48 h49 h50 h51.
          do! split.
          - rewrite size_cat to_uintD_small -h32 /=. smt().
            trivial.
          - rewrite to_uintD_small /= /#.
          - rewrite to_uintD_small /= -h32. smt().                  
            by apply (eq_mem_password_append Glob.mem{m1}
            (W64.of_int 1000) generatedPassword{m2} tmp8{m1} randomChar{m2}).
          - rewrite ultE to_uintD_small /=. smt().
            rewrite /EqWordInt in h42.
            by rewrite -h32 size_cat /= h42.
          - rewrite ultE to_uintD_small /=. smt().
            rewrite /EqWordInt in h42.
            by rewrite -h32 size_cat /= h42.
if{2}.
* (*conseq (_: false ==> _).
  - move => &m1 &m2 h1.
    have h2 : RPGRef.numbersSet{m2} = numbersSet by smt().
    have h3 : randomChar{m2} \in RPGRef.numbersSet{m2} by smt().
    rewrite h2 /numbersSet in h3.
    have h4 : 48 <= randomChar{m2} <= 57 by smt().
    have h5 : EqWordChar tmp8{m1} randomChar{m2} by smt().
    have h6 : !(tmp8{m1} \ule W8.of_int 122) by smt().
    rewrite /EqWordChar in h5.
    rewrite uleE lerNgt /= in h6.
    rewrite h5 in h6.
    smt().
  - trivial.*) admit.
* admit.

auto.
move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19
        h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35 h36 h37 h38 h39
        h40 h41 h42.
rewrite /EqWordInt in h42.
by rewrite ultE -h32 h42.
seq 2 1 : (#pre).
sp.
ecall (imp_ref_perm_equiv (W64.of_int 1000) generatedPassword{2}).
auto.
move => &m1 &m2 /> h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34.
have h35 : to_uint length{m1} = size generatedPassword{m2}.
+ admit. (*show that the generatedPw has the size of the policy length*)
do! split.
- by rewrite /EqWordInt.
- by rewrite -h35.
- by rewrite -h35.
- move => h36 h37 h38 rR memL.
  admit. (*still need to understand what is going on on this goal*)

seq 1 0 : (#pre).  
- auto.
  move => &m1 &m2 /> *.
  admit. (*append after size of pw is ok*)
sp.
if{1}.
+ conseq (_: false ==> _).
      - move => &m1 &m2 h1.
        have h2 : output{m1} = W64.one by smt().
        have h3 : to_sint output{m1} = to_sint W64.one.
        + smt().
        have h4 : output{m1} \slt W64.zero by smt().
        rewrite sltE h2 /= in h4.
        have h5 : 1 < 0.
        + admit. (*to_sint W64.one < to_sint W64.zero <=> 1 < 0 ??*)
        trivial.
      - trivial.

seq 1 0 : (#pre /\ pwd{1} = generatedPassword{2}).
- admit. (*ecall (pwdMemToSpec_eq Glob.mem{1} pwdAddr{1} policy{1}.`PassCertRPG_ref.length generatedPassword{2}). why not working? *)

sp.
auto.

(* if spec policy is unsat and mem policy is sat *)
conseq (_: false ==> _).
move => &m1 &m2 [[h1 [h2 [h3 h4]]] h5].
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 [h4 [h5 h6]]]]] h7] h8].
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
  smt().
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
  move => &m1 &m2 [[[[h1 [h2 [h3 h4]]] h5] h6] h7].
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
  smt().
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
  move => &m1 &m2 [[[h1 [h2 [h3 h4]]] h5] h6].
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
  smt().
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
qed.


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

lemma concrete_rpg_security policy :
  policyFitsW64 policy =>
  equiv [IdealRPG.generate_password ~ ConcreteScheme.generate_password : ={policy} ==> ={res}].
proof.
admitted.
