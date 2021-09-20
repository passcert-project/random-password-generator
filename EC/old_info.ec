lemma imp_policy_to_mem _policy _mem _policyAddr :
  hoare[ConcreteScheme.policySpecToMem : policy = _policy /\
                                         mem = _mem /\
                                         addr = _policyAddr /\
                                         policyFitsW64 _policy
         ==> 
        policyInMem _policy res _policyAddr].
proof.
proc.
seq 1 : (policy = _policy /\
         addr = _policyAddr /\
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
  split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               8
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`lowercaseMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.  
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+16)) policy.`lowercaseMax).
- wp.
  skip.
  move => &m /> ????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               16
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`lowercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               16
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`lowercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+24)) policy.`uppercaseMin).
- wp.
  skip.
  move => &m /> ?????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               24
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`uppercaseMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               24
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`uppercaseMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               24
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`uppercaseMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+32)) policy.`uppercaseMax).
- wp.
  skip.
  move => &m /> ??????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               32
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`uppercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               32
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`uppercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               32
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`uppercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               24
               32
               (of_int%W64 policy{m}.`uppercaseMin)
               (of_int%W64 policy{m}.`uppercaseMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+40)) policy.`numbersMin).
- wp.
  skip.
  move => &m /> ???????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               40
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`numbersMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               40
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`numbersMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               40
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`numbersMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               24
               40
               (of_int%W64 policy{m}.`uppercaseMin)
               (of_int%W64 policy{m}.`numbersMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               32
               40
               (of_int%W64 policy{m}.`uppercaseMax)
               (of_int%W64 policy{m}.`numbersMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+48)) policy.`numbersMax).
- wp.
  skip.
  move => &m /> ????????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               48
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               48
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               48
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               24
               48
               (of_int%W64 policy{m}.`uppercaseMin)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               32
               48
               (of_int%W64 policy{m}.`uppercaseMax)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               40
               48
               (of_int%W64 policy{m}.`numbersMin)
               (of_int%W64 policy{m}.`numbersMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+56)) policy.`specialMin).
- wp.
  skip.
  move => &m /> ?????????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               56
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               56
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               56
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               24
               56
               (of_int%W64 policy{m}.`uppercaseMin)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               32
               56
               (of_int%W64 policy{m}.`uppercaseMax)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               40
               56
               (of_int%W64 policy{m}.`numbersMin)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               48
               56
               (of_int%W64 policy{m}.`numbersMax)
               (of_int%W64 policy{m}.`specialMin)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
seq 1 : (#[/:]pre /\ EqWordInt (loadW64 mem ((to_uint addr)+64)) policy.`specialMax).
- wp.
  skip.
  move => &m /> ??????????????????????????.
  do! split.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               0
               64
               (of_int%W64 policy{m}.`length)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               8
               64
               (of_int%W64 policy{m}.`lowercaseMin)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               16
               64
               (of_int%W64 policy{m}.`lowercaseMax)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               24
               64
               (of_int%W64 policy{m}.`uppercaseMin)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               32
               64
               (of_int%W64 policy{m}.`uppercaseMax)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               40
               64
               (of_int%W64 policy{m}.`numbersMin)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               48
               64
               (of_int%W64 policy{m}.`numbersMax)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite (load_from_unaffected_store mem{m}
               (to_uint addr{m})
               56
               64
               (of_int%W64 policy{m}.`specialMin)
               (of_int%W64 policy{m}.`specialMax)).
    smt.
    trivial.
    by apply eqwordint_int_id.
  * rewrite load_from_store /EqWordInt to_uint_small.
    smt.
    reflexivity.
by skip.
qed.