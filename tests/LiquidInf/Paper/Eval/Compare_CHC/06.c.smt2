(set-info :original "/tmp/sea-nNhnns/06.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.preheader (Int Int Int Int Int ))
(declare-rel main@_bb (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_21_0 Bool )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Bool )
(declare-var main@%x.1.i.lcssa.lcssa_1 Int )
(declare-var main@%y.1.i.lcssa.lcssa_1 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%y.2.i.lcssa_1 Int )
(declare-var main@%.x.1.i.lcssa_1 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%y.1.i2_2 Int )
(declare-var main@%x.1.i1_2 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%w.0.i6_2 Int )
(declare-var main@%z.0.i5_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@.preheader.preheader_0 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%y.0.i7_0 Int )
(declare-var main@%w.0.i6_0 Int )
(declare-var main@%z.0.i5_0 Int )
(declare-var main@%x.0.i4_0 Int )
(declare-var main@%y.0.i7_1 Int )
(declare-var main@%w.0.i6_1 Int )
(declare-var main@%z.0.i5_1 Int )
(declare-var main@%x.0.i4_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%y.0.i.lcssa_0 Int )
(declare-var main@%x.0.i.lcssa_0 Int )
(declare-var main@%y.0.i.lcssa_1 Int )
(declare-var main@%x.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%y.1.i.lcssa_0 Int )
(declare-var main@%x.1.i.lcssa_0 Int )
(declare-var main@%y.1.i.lcssa_1 Int )
(declare-var main@%x.1.i.lcssa_1 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@%y.0.i7_2 Int )
(declare-var main@%x.0.i4_2 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%y.1.i2_0 Int )
(declare-var main@%x.1.i1_0 Int )
(declare-var main@%y.1.i2_1 Int )
(declare-var main@%x.1.i1_1 Int )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%x.1.i.lcssa.lcssa_0 Int )
(declare-var main@%y.1.i.lcssa.lcssa_0 Int )
(declare-var main@%.x.1.i_0 Int )
(declare-var main@%y.2.i_0 Int )
(declare-var main@._crit_edge.loopexit_0 Bool )
(declare-var main@%y.2.i.lcssa_0 Int )
(declare-var main@%.x.1.i.lcssa_0 Int )
(declare-var main@_bb_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@.preheader.preheader_0
             (and main@.preheader.preheader_0 main@entry_0))
         (=> (and main@.preheader.preheader_0 main@entry_0) (not main@%_2_0))
         (=> main@.preheader_0
             (and main@.preheader_0 main@.preheader.preheader_0))
         main@.preheader_0
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%y.0.i7_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%w.0.i6_0 1))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%z.0.i5_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%x.0.i4_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%y.0.i7_1 main@%y.0.i7_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%w.0.i6_1 main@%w.0.i6_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%z.0.i5_1 main@%z.0.i5_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%x.0.i4_1 main@%x.0.i4_0)))
    (main@.preheader @__VERIFIER_nondet_int_0
                     main@%y.0.i7_1
                     main@%w.0.i6_1
                     main@%z.0.i5_1
                     main@%x.0.i4_1)))
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
                    (= main@%_21_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.preheader @__VERIFIER_nondet_int_0
                                 main@%y.0.i7_0
                                 main@%w.0.i6_0
                                 main@%z.0.i5_0
                                 main@%x.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) main@%_5_0)
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%y.1.i.lcssa_0 main@%y.0.i7_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%x.1.i.lcssa_0 main@%x.0.i4_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%_16_0 (+ main@%y.1.i.lcssa_1 main@%x.1.i.lcssa_1)))
                (=> main@._crit_edge_0 (= main@%_17_0 (+ main@%_16_0 1)))
                (=> main@._crit_edge_0 (= main@%_18_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_19_0 0)))
                (=> main@.preheader_1
                    (and main@.preheader_1 main@._crit_edge_0))
                main@.preheader_1
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (not main@%_20_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%y.0.i7_1 main@%y.1.i.lcssa_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%w.0.i6_1 main@%_17_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%z.0.i5_1 main@%_16_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%x.0.i4_1 main@%x.1.i.lcssa_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%y.0.i7_2 main@%y.0.i7_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%w.0.i6_2 main@%w.0.i6_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%z.0.i5_2 main@%z.0.i5_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%x.0.i4_2 main@%x.0.i4_1)))))
  (=> a!1
      (main@.preheader @__VERIFIER_nondet_int_0
                       main@%y.0.i7_2
                       main@%w.0.i6_2
                       main@%z.0.i5_2
                       main@%x.0.i4_2))))
(rule (let ((a!1 (and (main@.preheader @__VERIFIER_nondet_int_0
                                 main@%y.0.i7_0
                                 main@%w.0.i6_0
                                 main@%z.0.i5_0
                                 main@%x.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (not main@%_5_0))
                (=> main@.lr.ph_0 (= main@%_6_0 (rem main@%w.0.i6_0 2)))
                (=> main@.lr.ph_0 (= main@%_7_0 (= main@%_6_0 1)))
                (=> main@.lr.ph_0 (= main@%_8_0 (ite main@%_7_0 1 0)))
                (=> main@.lr.ph_0 (= main@%_9_0 (rem main@%z.0.i5_0 2)))
                (=> main@.lr.ph_0 (= main@%_10_0 (= main@%_9_0 0)))
                (=> main@.lr.ph_0 (= main@%_11_0 (ite main@%_10_0 1 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.1.i2_0 main@%y.0.i7_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%x.1.i1_0 main@%x.0.i4_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.1.i2_1 main@%y.1.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%x.1.i1_1 main@%x.1.i1_0)))))
  (=> a!1
      (main@_bb @__VERIFIER_nondet_int_0
                main@%x.1.i1_1
                main@%_8_0
                main@%y.1.i2_1
                main@%_11_0))))
(rule (let ((a!1 (and (main@.preheader @__VERIFIER_nondet_int_0
                                 main@%y.0.i7_0
                                 main@%w.0.i6_0
                                 main@%z.0.i5_0
                                 main@%x.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) main@%_5_0)
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%y.1.i.lcssa_0 main@%y.0.i7_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%x.1.i.lcssa_0 main@%x.0.i4_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%_16_0 (+ main@%y.1.i.lcssa_1 main@%x.1.i.lcssa_1)))
                (=> main@._crit_edge_0 (= main@%_17_0 (+ main@%_16_0 1)))
                (=> main@._crit_edge_0 (= main@%_18_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_19_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@._crit_edge_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    main@%_20_0)
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%x.1.i.lcssa.lcssa_0 main@%x.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%y.1.i.lcssa.lcssa_0 main@%y.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%x.1.i.lcssa.lcssa_1 main@%x.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
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
                    (= main@%_21_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@_bb @__VERIFIER_nondet_int_0
                          main@%x.1.i1_0
                          main@%_8_0
                          main@%y.1.i2_0
                          main@%_11_0)
                true
                (= main@%.x.1.i_0 (+ main@%x.1.i1_0 main@%_8_0))
                (= main@%y.2.i_0 (+ main@%y.1.i2_0 main@%_11_0))
                (= main@%_13_0 @__VERIFIER_nondet_int_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0) main@%_15_0)
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_0 main@%y.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_0 main@%.x.1.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_1 main@%y.2.i.lcssa_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_1 main@%.x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%y.1.i.lcssa_0 main@%y.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%x.1.i.lcssa_0 main@%.x.1.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%_16_0 (+ main@%y.1.i.lcssa_1 main@%x.1.i.lcssa_1)))
                (=> main@._crit_edge_0 (= main@%_17_0 (+ main@%_16_0 1)))
                (=> main@._crit_edge_0 (= main@%_18_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_19_0 0)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@._crit_edge_0))
                main@.preheader_0
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (not main@%_20_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%y.0.i7_0 main@%y.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%w.0.i6_0 main@%_17_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%z.0.i5_0 main@%_16_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%x.0.i4_0 main@%x.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%y.0.i7_1 main@%y.0.i7_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%w.0.i6_1 main@%w.0.i6_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%z.0.i5_1 main@%z.0.i5_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%x.0.i4_1 main@%x.0.i4_0)))))
  (=> a!1
      (main@.preheader @__VERIFIER_nondet_int_0
                       main@%y.0.i7_1
                       main@%w.0.i6_1
                       main@%z.0.i5_1
                       main@%x.0.i4_1))))
(rule (=> (and (main@_bb @__VERIFIER_nondet_int_0
                   main@%x.1.i1_0
                   main@%_8_0
                   main@%y.1.i2_0
                   main@%_11_0)
         true
         (= main@%.x.1.i_0 (+ main@%x.1.i1_0 main@%_8_0))
         (= main@%y.2.i_0 (+ main@%y.1.i2_0 main@%_11_0))
         (= main@%_13_0 @__VERIFIER_nondet_int_0)
         (= main@%_15_0 (= main@%_14_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_15_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.1.i2_1 main@%y.2.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.1.i1_1 main@%.x.1.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.1.i2_2 main@%y.1.i2_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.1.i1_2 main@%x.1.i1_1)))
    (main@_bb @__VERIFIER_nondet_int_0
              main@%x.1.i1_2
              main@%_8_0
              main@%y.1.i2_2
              main@%_11_0)))
(rule (let ((a!1 (and (main@_bb @__VERIFIER_nondet_int_0
                          main@%x.1.i1_0
                          main@%_8_0
                          main@%y.1.i2_0
                          main@%_11_0)
                true
                (= main@%.x.1.i_0 (+ main@%x.1.i1_0 main@%_8_0))
                (= main@%y.2.i_0 (+ main@%y.1.i2_0 main@%_11_0))
                (= main@%_13_0 @__VERIFIER_nondet_int_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0) main@%_15_0)
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_0 main@%y.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_0 main@%.x.1.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%y.2.i.lcssa_1 main@%y.2.i.lcssa_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%.x.1.i.lcssa_1 main@%.x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%y.1.i.lcssa_0 main@%y.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%x.1.i.lcssa_0 main@%.x.1.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%x.1.i.lcssa_1 main@%x.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%_16_0 (+ main@%y.1.i.lcssa_1 main@%x.1.i.lcssa_1)))
                (=> main@._crit_edge_0 (= main@%_17_0 (+ main@%_16_0 1)))
                (=> main@._crit_edge_0 (= main@%_18_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_19_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@._crit_edge_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    main@%_20_0)
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%x.1.i.lcssa.lcssa_0 main@%x.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%y.1.i.lcssa.lcssa_0 main@%y.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%x.1.i.lcssa.lcssa_1 main@%x.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
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
                    (= main@%_21_0 (= main@%x.0.i.lcssa_1 main@%y.0.i.lcssa_1)))
                (=> main@verifier.error_0 (not main@%_21_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

