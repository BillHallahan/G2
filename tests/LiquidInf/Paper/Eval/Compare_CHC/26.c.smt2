(set-info :original "/tmp/sea-fNO1n4/26.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.preheader1 (Int Int Int Int Int ))
(declare-rel main@_bb (Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph5 (Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_27_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%x.1.i.lcssa.lcssa_1 Int )
(declare-var main@%y.1.i.lcssa.lcssa_1 Int )
(declare-var main@%_24_0 Int )
(declare-var main@%_25_0 Int )
(declare-var main@%_26_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%_21_0 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Bool )
(declare-var main@%y.2.i.lcssa_1 Int )
(declare-var main@%.x.1.i.lcssa_1 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%y.1.i3_2 Int )
(declare-var main@%x.1.i2_2 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@.preheader1.preheader_0 Bool )
(declare-var main@.preheader1_0 Bool )
(declare-var main@%y.0.i11_0 Int )
(declare-var main@%w.0.i10_0 Int )
(declare-var main@%z.0.i9_0 Int )
(declare-var main@%x.0.i8_0 Int )
(declare-var main@%y.0.i11_1 Int )
(declare-var main@%w.0.i10_1 Int )
(declare-var main@%z.0.i9_1 Int )
(declare-var main@%x.0.i8_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%y.0.i.lcssa_0 Int )
(declare-var main@%x.0.i.lcssa_0 Int )
(declare-var main@%y.0.i.lcssa_1 Int )
(declare-var main@%x.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%y.1.i.lcssa_0 Int )
(declare-var main@%x.1.i.lcssa_0 Int )
(declare-var main@%y.1.i.lcssa_1 Int )
(declare-var main@%x.1.i.lcssa_1 Int )
(declare-var main@.loopexit_0 Bool )
(declare-var main@%w.1.i.lcssa_0 Int )
(declare-var main@%z.1.i.lcssa_0 Int )
(declare-var main@%w.1.i.lcssa_1 Int )
(declare-var main@%z.1.i.lcssa_1 Int )
(declare-var main@.preheader1_1 Bool )
(declare-var main@%y.0.i11_2 Int )
(declare-var main@%w.0.i10_2 Int )
(declare-var main@%z.0.i9_2 Int )
(declare-var main@%x.0.i8_2 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_16_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%y.1.i3_0 Int )
(declare-var main@%x.1.i2_0 Int )
(declare-var main@%y.1.i3_1 Int )
(declare-var main@%x.1.i2_1 Int )
(declare-var main@.lr.ph5.preheader_0 Bool )
(declare-var main@.lr.ph5_0 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%x.1.i.lcssa.lcssa_0 Int )
(declare-var main@%y.1.i.lcssa.lcssa_0 Int )
(declare-var main@%.x.1.i_0 Int )
(declare-var main@%y.2.i_0 Int )
(declare-var main@.preheader.loopexit_0 Bool )
(declare-var main@%y.2.i.lcssa_0 Int )
(declare-var main@%.x.1.i.lcssa_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@..loopexit_crit_edge_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@.lr.ph5_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@.preheader1.preheader_0
             (and main@.preheader1.preheader_0 main@entry_0))
         (=> (and main@.preheader1.preheader_0 main@entry_0) (not main@%_2_0))
         (=> main@.preheader1_0
             (and main@.preheader1_0 main@.preheader1.preheader_0))
         main@.preheader1_0
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%y.0.i11_0 0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%w.0.i10_0 1))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%z.0.i9_0 0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%x.0.i8_0 0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%y.0.i11_1 main@%y.0.i11_0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%w.0.i10_1 main@%w.0.i10_0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%z.0.i9_1 main@%z.0.i9_0))
         (=> (and main@.preheader1_0 main@.preheader1.preheader_0)
             (= main@%x.0.i8_1 main@%x.0.i8_0)))
    (main@.preheader1 @__VERIFIER_nondet_int_0
                      main@%y.0.i11_1
                      main@%w.0.i10_1
                      main@%z.0.i9_1
                      main@%x.0.i8_1)))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_2_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%y.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%x.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_27_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_27_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.preheader1 @__VERIFIER_nondet_int_0
                                  main@%y.0.i11_0
                                  main@%w.0.i10_0
                                  main@%z.0.i9_0
                                  main@%x.0.i8_0)
                true
                (= main@%_8_0 @__VERIFIER_nondet_int_0)
                (= main@%_10_0 (= main@%_9_0 0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) main@%_10_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_0 main@%y.0.i11_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_0 main@%x.0.i8_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.preheader_0))
                (=> (and main@.loopexit_0 main@.preheader_0) main@%_19_0)
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_0 main@%w.0.i10_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_0 main@%z.0.i9_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@.preheader1_1
                    (and main@.preheader1_1 main@.loopexit_0))
                main@.preheader1_1
                (=> (and main@.preheader1_1 main@.loopexit_0) (not main@%_7_0))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%y.0.i11_1 main@%y.1.i.lcssa_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%w.0.i10_1 main@%w.1.i.lcssa_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%z.0.i9_1 main@%z.1.i.lcssa_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%x.0.i8_1 main@%x.1.i.lcssa_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%y.0.i11_2 main@%y.0.i11_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%w.0.i10_2 main@%w.0.i10_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%z.0.i9_2 main@%z.0.i9_1))
                (=> (and main@.preheader1_1 main@.loopexit_0)
                    (= main@%x.0.i8_2 main@%x.0.i8_1)))))
  (=> a!1
      (main@.preheader1 @__VERIFIER_nondet_int_0
                        main@%y.0.i11_2
                        main@%w.0.i10_2
                        main@%z.0.i9_2
                        main@%x.0.i8_2))))
(rule (let ((a!1 (and (main@.preheader1 @__VERIFIER_nondet_int_0
                                  main@%y.0.i11_0
                                  main@%w.0.i10_0
                                  main@%z.0.i9_0
                                  main@%x.0.i8_0)
                true
                (= main@%_8_0 @__VERIFIER_nondet_int_0)
                (= main@%_10_0 (= main@%_9_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader1_0))
                (=> (and main@.lr.ph_0 main@.preheader1_0) (not main@%_10_0))
                (=> main@.lr.ph_0 (= main@%_11_0 (rem main@%w.0.i10_0 2)))
                (=> main@.lr.ph_0 (= main@%_12_0 (= main@%_11_0 1)))
                (=> main@.lr.ph_0 (= main@%_13_0 (ite main@%_12_0 1 0)))
                (=> main@.lr.ph_0 (= main@%_14_0 (rem main@%z.0.i9_0 2)))
                (=> main@.lr.ph_0 (= main@%_15_0 (= main@%_14_0 0)))
                (=> main@.lr.ph_0 (= main@%_16_0 (ite main@%_15_0 1 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.1.i3_0 main@%y.0.i11_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%x.1.i2_0 main@%x.0.i8_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.1.i3_1 main@%y.1.i3_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%x.1.i2_1 main@%x.1.i2_0)))))
  (=> a!1
      (main@_bb @__VERIFIER_nondet_int_0
                main@%w.0.i10_0
                main@%z.0.i9_0
                main@%x.1.i2_1
                main@%_13_0
                main@%y.1.i3_1
                main@%_16_0))))
(rule (let ((a!1 (and (main@.preheader1 @__VERIFIER_nondet_int_0
                                  main@%y.0.i11_0
                                  main@%w.0.i10_0
                                  main@%z.0.i9_0
                                  main@%x.0.i8_0)
                true
                (= main@%_8_0 @__VERIFIER_nondet_int_0)
                (= main@%_10_0 (= main@%_9_0 0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) main@%_10_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_0 main@%y.0.i11_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_0 main@%x.0.i8_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.lr.ph5.preheader_0
                    (and main@.lr.ph5.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph5.preheader_0 main@.preheader_0)
                    (not main@%_19_0))
                (=> main@.lr.ph5_0
                    (and main@.lr.ph5_0 main@.lr.ph5.preheader_0))
                main@.lr.ph5_0)))
  (=> a!1
      (main@.lr.ph5 @__VERIFIER_nondet_int_0
                    main@%x.1.i.lcssa_1
                    main@%y.1.i.lcssa_1))))
(rule (let ((a!1 (and (main@.preheader1 @__VERIFIER_nondet_int_0
                                  main@%y.0.i11_0
                                  main@%w.0.i10_0
                                  main@%z.0.i9_0
                                  main@%x.0.i8_0)
                true
                (= main@%_8_0 @__VERIFIER_nondet_int_0)
                (= main@%_10_0 (= main@%_9_0 0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader1_0))
                (=> (and main@.preheader_0 main@.preheader1_0) main@%_10_0)
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_0 main@%y.0.i11_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_0 main@%x.0.i8_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader1_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.preheader_0))
                (=> (and main@.loopexit_0 main@.preheader_0) main@%_19_0)
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_0 main@%w.0.i10_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_0 main@%z.0.i9_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.loopexit_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    main@%_7_0)
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_0 main@%x.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_0 main@%y.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_1 main@%x.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_1 main@%y.1.i.lcssa.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_0 main@%y.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_0 main@%x.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_27_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_27_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@_bb @__VERIFIER_nondet_int_0
                          main@%w.0.i10_0
                          main@%z.0.i9_0
                          main@%x.1.i2_0
                          main@%_13_0
                          main@%y.1.i3_0
                          main@%_16_0)
                true
                (= main@%.x.1.i_0 (+ main@%x.1.i2_0 main@%_13_0))
                (= main@%y.2.i_0 (+ main@%y.1.i3_0 main@%_16_0))
                (= main@%_21_0 @__VERIFIER_nondet_int_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (=> main@.preheader.loopexit_0
                    (and main@.preheader.loopexit_0 main@_bb_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0) main@%_23_0)
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_0 main@%y.2.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_0 main@%.x.1.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_1 main@%y.2.i.lcssa_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_1 main@%.x.1.i.lcssa_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader.loopexit_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_0 main@%y.2.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_0 main@%.x.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.preheader_0))
                (=> (and main@.loopexit_0 main@.preheader_0) main@%_19_0)
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_0 main@%w.0.i10_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_0 main@%z.0.i9_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.loopexit_0))
                main@.preheader1_0
                (=> (and main@.preheader1_0 main@.loopexit_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%y.0.i11_0 main@%y.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%w.0.i10_1 main@%w.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%z.0.i9_1 main@%z.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%x.0.i8_0 main@%x.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%y.0.i11_1 main@%y.0.i11_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%w.0.i10_2 main@%w.0.i10_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%z.0.i9_2 main@%z.0.i9_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%x.0.i8_1 main@%x.0.i8_0)))))
  (=> a!1
      (main@.preheader1 @__VERIFIER_nondet_int_0
                        main@%y.0.i11_1
                        main@%w.0.i10_2
                        main@%z.0.i9_2
                        main@%x.0.i8_1))))
(rule (=> (and (main@_bb @__VERIFIER_nondet_int_0
                   main@%w.0.i10_0
                   main@%z.0.i9_0
                   main@%x.1.i2_0
                   main@%_13_0
                   main@%y.1.i3_0
                   main@%_16_0)
         true
         (= main@%.x.1.i_0 (+ main@%x.1.i2_0 main@%_13_0))
         (= main@%y.2.i_0 (+ main@%y.1.i3_0 main@%_16_0))
         (= main@%_21_0 @__VERIFIER_nondet_int_0)
         (= main@%_23_0 (= main@%_22_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_23_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.1.i3_1 main@%y.2.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.1.i2_1 main@%.x.1.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.1.i3_2 main@%y.1.i3_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.1.i2_2 main@%x.1.i2_1)))
    (main@_bb @__VERIFIER_nondet_int_0
              main@%w.0.i10_0
              main@%z.0.i9_0
              main@%x.1.i2_2
              main@%_13_0
              main@%y.1.i3_2
              main@%_16_0)))
(rule (let ((a!1 (and (main@_bb @__VERIFIER_nondet_int_0
                          main@%w.0.i10_0
                          main@%z.0.i9_0
                          main@%x.1.i2_0
                          main@%_13_0
                          main@%y.1.i3_0
                          main@%_16_0)
                true
                (= main@%.x.1.i_0 (+ main@%x.1.i2_0 main@%_13_0))
                (= main@%y.2.i_0 (+ main@%y.1.i3_0 main@%_16_0))
                (= main@%_21_0 @__VERIFIER_nondet_int_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (=> main@.preheader.loopexit_0
                    (and main@.preheader.loopexit_0 main@_bb_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0) main@%_23_0)
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_0 main@%y.2.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_0 main@%.x.1.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_1 main@%y.2.i.lcssa_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_1 main@%.x.1.i.lcssa_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader.loopexit_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_0 main@%y.2.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_0 main@%.x.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.lr.ph5.preheader_0
                    (and main@.lr.ph5.preheader_0 main@.preheader_0))
                (=> (and main@.lr.ph5.preheader_0 main@.preheader_0)
                    (not main@%_19_0))
                (=> main@.lr.ph5_0
                    (and main@.lr.ph5_0 main@.lr.ph5.preheader_0))
                main@.lr.ph5_0)))
  (=> a!1
      (main@.lr.ph5 @__VERIFIER_nondet_int_0
                    main@%x.1.i.lcssa_1
                    main@%y.1.i.lcssa_1))))
(rule (let ((a!1 (and (main@_bb @__VERIFIER_nondet_int_0
                          main@%w.0.i10_0
                          main@%z.0.i9_0
                          main@%x.1.i2_0
                          main@%_13_0
                          main@%y.1.i3_0
                          main@%_16_0)
                true
                (= main@%.x.1.i_0 (+ main@%x.1.i2_0 main@%_13_0))
                (= main@%y.2.i_0 (+ main@%y.1.i3_0 main@%_16_0))
                (= main@%_21_0 @__VERIFIER_nondet_int_0)
                (= main@%_23_0 (= main@%_22_0 0))
                (=> main@.preheader.loopexit_0
                    (and main@.preheader.loopexit_0 main@_bb_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0) main@%_23_0)
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_0 main@%y.2.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_0 main@%.x.1.i_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_1 main@%y.2.i.lcssa_0))
                (=> (and main@.preheader.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_1 main@%.x.1.i.lcssa_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader.loopexit_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_0 main@%y.2.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_0 main@%.x.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_17_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_19_0 (= main@%_18_0 0)))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.preheader_0))
                (=> (and main@.loopexit_0 main@.preheader_0) main@%_19_0)
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_0 main@%w.0.i10_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_0 main@%z.0.i9_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.preheader_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.loopexit_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    main@%_7_0)
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_0 main@%x.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_0 main@%y.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_1 main@%x.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_1 main@%y.1.i.lcssa.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_0 main@%y.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_0 main@%x.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_27_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_27_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.lr.ph5 @__VERIFIER_nondet_int_0
                              main@%x.1.i.lcssa_0
                              main@%y.1.i.lcssa_0)
                true
                (= main@%_24_0 @__VERIFIER_nondet_int_0)
                (= main@%_26_0 (= main@%_25_0 0))
                (=> main@..loopexit_crit_edge_0
                    (and main@..loopexit_crit_edge_0 main@.lr.ph5_0))
                (=> (and main@..loopexit_crit_edge_0 main@.lr.ph5_0)
                    main@%_26_0)
                (=> main@..loopexit_crit_edge_0
                    (= main@%_3_0 (+ main@%y.1.i.lcssa_0 main@%x.1.i.lcssa_0)))
                (=> main@..loopexit_crit_edge_0 (= main@%_4_0 (+ main@%_3_0 1)))
                (=> main@.loopexit_0
                    (and main@.loopexit_0 main@..loopexit_crit_edge_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%w.1.i.lcssa_0 main@%_4_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%z.1.i.lcssa_0 main@%_3_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@.preheader1_0
                    (and main@.preheader1_0 main@.loopexit_0))
                main@.preheader1_0
                (=> (and main@.preheader1_0 main@.loopexit_0) (not main@%_7_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%y.0.i11_0 main@%y.1.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%w.0.i10_0 main@%w.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%z.0.i9_0 main@%z.1.i.lcssa_1))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%x.0.i8_0 main@%x.1.i.lcssa_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%y.0.i11_1 main@%y.0.i11_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%w.0.i10_1 main@%w.0.i10_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%z.0.i9_1 main@%z.0.i9_0))
                (=> (and main@.preheader1_0 main@.loopexit_0)
                    (= main@%x.0.i8_1 main@%x.0.i8_0)))))
  (=> a!1
      (main@.preheader1 @__VERIFIER_nondet_int_0
                        main@%y.0.i11_1
                        main@%w.0.i10_1
                        main@%z.0.i9_1
                        main@%x.0.i8_1))))
(rule (=> (and (main@.lr.ph5 @__VERIFIER_nondet_int_0
                       main@%x.1.i.lcssa_0
                       main@%y.1.i.lcssa_0)
         true
         (= main@%_24_0 @__VERIFIER_nondet_int_0)
         (= main@%_26_0 (= main@%_25_0 0))
         (=> main@.lr.ph5_1 (and main@.lr.ph5_1 main@.lr.ph5_0))
         main@.lr.ph5_1
         (=> (and main@.lr.ph5_1 main@.lr.ph5_0) (not main@%_26_0)))
    (main@.lr.ph5 @__VERIFIER_nondet_int_0
                  main@%x.1.i.lcssa_0
                  main@%y.1.i.lcssa_0)))
(rule (let ((a!1 (and (main@.lr.ph5 @__VERIFIER_nondet_int_0
                              main@%x.1.i.lcssa_0
                              main@%y.1.i.lcssa_0)
                true
                (= main@%_24_0 @__VERIFIER_nondet_int_0)
                (= main@%_26_0 (= main@%_25_0 0))
                (=> main@..loopexit_crit_edge_0
                    (and main@..loopexit_crit_edge_0 main@.lr.ph5_0))
                (=> (and main@..loopexit_crit_edge_0 main@.lr.ph5_0)
                    main@%_26_0)
                (=> main@..loopexit_crit_edge_0
                    (= main@%_3_0 (+ main@%y.1.i.lcssa_0 main@%x.1.i.lcssa_0)))
                (=> main@..loopexit_crit_edge_0 (= main@%_4_0 (+ main@%_3_0 1)))
                (=> main@.loopexit_0
                    (and main@.loopexit_0 main@..loopexit_crit_edge_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%w.1.i.lcssa_0 main@%_4_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%z.1.i.lcssa_0 main@%_3_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%w.1.i.lcssa_1 main@%w.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@..loopexit_crit_edge_0)
                    (= main@%z.1.i.lcssa_1 main@%z.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_5_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_7_0 (= main@%_6_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.loopexit_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    main@%_7_0)
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_0 main@%x.1.i.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_0 main@%y.1.i.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%x.1.i.lcssa.lcssa_1 main@%x.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%y.1.i.lcssa.lcssa_1 main@%y.1.i.lcssa.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_0 main@%y.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_0 main@%x.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%x.0.i.lcssa_1 main@%x.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_27_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_27_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

