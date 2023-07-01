(set-info :original "/tmp/sea-Lnudm8/20.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph.preheader (Int Bool Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Bool Int Int Int Int Int Int Int ))
(declare-rel main@._crit_edge.loopexit (Int Bool Int Int Int Int ))
(declare-rel main@._crit_edge (Int Int Bool Int Int Int ))
(declare-rel main@_un (Int Int Bool ))
(declare-rel main@_un1 (Int Int ))
(declare-rel main@verifier.error ())
(declare-var main@%_26_0 Bool )
(declare-var main@%_24_0 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Bool )
(declare-var main@%_15_0 Bool )
(declare-var main@%y.1.v.i_0 Int )
(declare-var main@%x.1.v.i_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_5_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%m.0.i.lcssa_0 Int )
(declare-var main@%x.0.i.lcssa_0 Int )
(declare-var main@%y.0.i.lcssa_0 Int )
(declare-var main@%m.0.i4_0 Int )
(declare-var main@%x.0.i3_0 Int )
(declare-var main@%y.0.i2_0 Int )
(declare-var main@%j.0.i1_0 Int )
(declare-var main@%y.1.i_0 Int )
(declare-var main@%x.1.i_0 Int )
(declare-var main@%m.0.j.0.i_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%m.0.i4_1 Int )
(declare-var main@%x.0.i3_1 Int )
(declare-var main@%y.0.i2_1 Int )
(declare-var main@%j.0.i1_1 Int )
(declare-var main@%m.0.j.0.i.lcssa_0 Int )
(declare-var main@%x.1.i.lcssa_0 Int )
(declare-var main@%y.1.i.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 @__VERIFIER_nondet_int_0)
         (= main@%_4_0 @__VERIFIER_nondet_int_0)
         (= main@%_6_0 @__VERIFIER_nondet_int_0)
         (= main@%_8_0 @__VERIFIER_nondet_int_0)
         (= main@%_10_0 @__VERIFIER_nondet_int_0)
         (= main@%_12_0 (+ main@%_3_0 main@%_1_0))
         (= main@%_13_0 (= main@%_12_0 main@%_5_0))
         main@%_13_0
         (= main@%_14_0 (< 0 main@%_11_0))
         main@%_14_0)
    (main@.lr.ph.preheader
      main@%_11_0
      main@%_14_0
      main@%_5_0
      main@%_9_0
      @__VERIFIER_nondet_int_0
      main@%_1_0
      main@%_3_0)))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 @__VERIFIER_nondet_int_0)
         (= main@%_4_0 @__VERIFIER_nondet_int_0)
         (= main@%_6_0 @__VERIFIER_nondet_int_0)
         (= main@%_8_0 @__VERIFIER_nondet_int_0)
         (= main@%_10_0 @__VERIFIER_nondet_int_0)
         (= main@%_12_0 (+ main@%_3_0 main@%_1_0))
         (= main@%_13_0 (= main@%_12_0 main@%_5_0))
         main@%_13_0
         (= main@%_14_0 (< 0 main@%_11_0))
         (not main@%_14_0)
         (= main@%m.0.i.lcssa_0 0)
         (= main@%x.0.i.lcssa_0 main@%_1_0)
         (= main@%y.0.i.lcssa_0 main@%_3_0))
    (main@._crit_edge main@%m.0.i.lcssa_0
                      main@%_11_0
                      main@%_14_0
                      main@%x.0.i.lcssa_0
                      main@%y.0.i.lcssa_0
                      main@%_5_0)))
(rule (=> (and (main@.lr.ph.preheader
           main@%_11_0
           main@%_14_0
           main@%_5_0
           main@%_9_0
           @__VERIFIER_nondet_int_0
           main@%_1_0
           main@%_3_0)
         true
         (= main@%m.0.i4_0 0)
         (= main@%x.0.i3_0 main@%_1_0)
         (= main@%y.0.i2_0 main@%_3_0)
         (= main@%j.0.i1_0 0))
    (main@.lr.ph main@%_11_0
                 main@%_14_0
                 main@%_5_0
                 main@%j.0.i1_0
                 main@%_9_0
                 main@%y.0.i2_0
                 main@%x.0.i3_0
                 @__VERIFIER_nondet_int_0
                 main@%m.0.i4_0)))
(rule (=> (and (main@.lr.ph main@%_11_0
                      main@%_14_0
                      main@%_5_0
                      main@%j.0.i1_0
                      main@%_9_0
                      main@%y.0.i2_0
                      main@%x.0.i3_0
                      @__VERIFIER_nondet_int_0
                      main@%m.0.i4_0)
         true
         (= main@%_15_0 (= main@%j.0.i1_0 main@%_9_0))
         (= main@%y.1.v.i_0 (ite main@%_15_0 (- 1) 1))
         (= main@%y.1.i_0 (+ main@%y.1.v.i_0 main@%y.0.i2_0))
         (= main@%x.1.v.i_0 (ite main@%_15_0 1 (- 1)))
         (= main@%x.1.i_0 (+ main@%x.0.i3_0 main@%x.1.v.i_0))
         (= main@%_16_0 @__VERIFIER_nondet_int_0)
         (= main@%_18_0 (= main@%_17_0 0))
         (= main@%m.0.j.0.i_0 (ite main@%_18_0 main@%m.0.i4_0 main@%j.0.i1_0))
         (= main@%_19_0 (+ main@%j.0.i1_0 1))
         (= main@%_20_0 (< main@%_19_0 main@%_11_0))
         main@%_20_0
         (= main@%m.0.i4_1 main@%m.0.j.0.i_0)
         (= main@%x.0.i3_1 main@%x.1.i_0)
         (= main@%y.0.i2_1 main@%y.1.i_0)
         (= main@%j.0.i1_1 main@%_19_0))
    (main@.lr.ph main@%_11_0
                 main@%_14_0
                 main@%_5_0
                 main@%j.0.i1_1
                 main@%_9_0
                 main@%y.0.i2_1
                 main@%x.0.i3_1
                 @__VERIFIER_nondet_int_0
                 main@%m.0.i4_1)))
(rule (=> (and (main@.lr.ph main@%_11_0
                      main@%_14_0
                      main@%_5_0
                      main@%j.0.i1_0
                      main@%_9_0
                      main@%y.0.i2_0
                      main@%x.0.i3_0
                      @__VERIFIER_nondet_int_0
                      main@%m.0.i4_0)
         true
         (= main@%_15_0 (= main@%j.0.i1_0 main@%_9_0))
         (= main@%y.1.v.i_0 (ite main@%_15_0 (- 1) 1))
         (= main@%y.1.i_0 (+ main@%y.1.v.i_0 main@%y.0.i2_0))
         (= main@%x.1.v.i_0 (ite main@%_15_0 1 (- 1)))
         (= main@%x.1.i_0 (+ main@%x.0.i3_0 main@%x.1.v.i_0))
         (= main@%_16_0 @__VERIFIER_nondet_int_0)
         (= main@%_18_0 (= main@%_17_0 0))
         (= main@%m.0.j.0.i_0 (ite main@%_18_0 main@%m.0.i4_0 main@%j.0.i1_0))
         (= main@%_19_0 (+ main@%j.0.i1_0 1))
         (= main@%_20_0 (< main@%_19_0 main@%_11_0))
         (not main@%_20_0)
         (= main@%m.0.j.0.i.lcssa_0 main@%m.0.j.0.i_0)
         (= main@%x.1.i.lcssa_0 main@%x.1.i_0)
         (= main@%y.1.i.lcssa_0 main@%y.1.i_0))
    (main@._crit_edge.loopexit
      main@%_11_0
      main@%_14_0
      main@%_5_0
      main@%m.0.j.0.i.lcssa_0
      main@%x.1.i.lcssa_0
      main@%y.1.i.lcssa_0)))
(rule (=> (and (main@._crit_edge.loopexit
           main@%_11_0
           main@%_14_0
           main@%_5_0
           main@%m.0.j.0.i.lcssa_0
           main@%x.1.i.lcssa_0
           main@%y.1.i.lcssa_0)
         true
         (= main@%m.0.i.lcssa_0 main@%m.0.j.0.i.lcssa_0)
         (= main@%x.0.i.lcssa_0 main@%x.1.i.lcssa_0)
         (= main@%y.0.i.lcssa_0 main@%y.1.i.lcssa_0))
    (main@._crit_edge main@%m.0.i.lcssa_0
                      main@%_11_0
                      main@%_14_0
                      main@%x.0.i.lcssa_0
                      main@%y.0.i.lcssa_0
                      main@%_5_0)))
(rule (=> (and (main@._crit_edge main@%m.0.i.lcssa_0
                           main@%_11_0
                           main@%_14_0
                           main@%x.0.i.lcssa_0
                           main@%y.0.i.lcssa_0
                           main@%_5_0)
         true
         (= main@%_21_0 (+ main@%x.0.i.lcssa_0 main@%y.0.i.lcssa_0))
         (= main@%_22_0 (= main@%_21_0 main@%_5_0))
         main@%_22_0)
    (main@_un main@%m.0.i.lcssa_0 main@%_11_0 main@%_14_0)))
(rule (=> (and (main@._crit_edge main@%m.0.i.lcssa_0
                           main@%_11_0
                           main@%_14_0
                           main@%x.0.i.lcssa_0
                           main@%y.0.i.lcssa_0
                           main@%_5_0)
         true
         (= main@%_21_0 (+ main@%x.0.i.lcssa_0 main@%y.0.i.lcssa_0))
         (= main@%_22_0 (= main@%_21_0 main@%_5_0))
         (not main@%_22_0))
    main@verifier.error))
(rule (=> (and (main@_un main@%m.0.i.lcssa_0 main@%_11_0 main@%_14_0)
         true
         main@%_14_0
         (= main@%_24_0 (< (- 1) main@%m.0.i.lcssa_0))
         main@%_24_0)
    (main@_un1 main@%m.0.i.lcssa_0 main@%_11_0)))
(rule (=> (and (main@_un main@%m.0.i.lcssa_0 main@%_11_0 main@%_14_0)
         true
         main@%_14_0
         (= main@%_24_0 (< (- 1) main@%m.0.i.lcssa_0))
         (not main@%_24_0))
    main@verifier.error))
(rule (=> (and (main@_un1 main@%m.0.i.lcssa_0 main@%_11_0)
         true
         (= main@%_26_0 (< main@%m.0.i.lcssa_0 main@%_11_0))
         (not main@%_26_0))
    main@verifier.error))
(query main@verifier.error)

