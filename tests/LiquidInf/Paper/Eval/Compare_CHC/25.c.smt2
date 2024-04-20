(set-info :original "/tmp/sea-Aw2vzk/25.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.preheader (Int Int Int Int Int ))
(declare-rel main@_bb (Int Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_17_0 Bool )
(declare-var main@%not.1.i_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%i.1.i.lcssa.lcssa_1 Int )
(declare-var main@%j.1.i.lcssa.lcssa_1 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%j.2.i.lcssa_1 Int )
(declare-var main@%i.2.i.lcssa_1 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%not..i_0 Bool )
(declare-var main@%j.1.i2_2 Int )
(declare-var main@%i.1.i1_2 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@.preheader.preheader_0 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%j.0.i7_0 Int )
(declare-var main@%x.0.i6_0 Int )
(declare-var main@%y.0.i5_0 Int )
(declare-var main@%i.0.i4_0 Int )
(declare-var main@%j.0.i7_1 Int )
(declare-var main@%x.0.i6_1 Int )
(declare-var main@%y.0.i5_1 Int )
(declare-var main@%i.0.i4_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%j.0.i.lcssa_0 Int )
(declare-var main@%i.0.i.lcssa_0 Int )
(declare-var main@%j.0.i.lcssa_1 Int )
(declare-var main@%i.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%j.1.i.lcssa_0 Int )
(declare-var main@%i.1.i.lcssa_0 Int )
(declare-var main@%j.1.i.lcssa_1 Int )
(declare-var main@%i.1.i.lcssa_1 Int )
(declare-var main@%x.1.i_0 Int )
(declare-var main@%y.1.i_0 Int )
(declare-var main@.preheader_1 Bool )
(declare-var main@%j.0.i7_2 Int )
(declare-var main@%x.0.i6_2 Int )
(declare-var main@%y.0.i5_2 Int )
(declare-var main@%i.0.i4_2 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%j.1.i2_0 Int )
(declare-var main@%i.1.i1_0 Int )
(declare-var main@%j.1.i2_1 Int )
(declare-var main@%i.1.i1_1 Int )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%i.1.i.lcssa.lcssa_0 Int )
(declare-var main@%j.1.i.lcssa.lcssa_0 Int )
(declare-var main@%i.2.i_0 Int )
(declare-var main@%j.2.i_0 Int )
(declare-var main@._crit_edge.loopexit_0 Bool )
(declare-var main@%j.2.i.lcssa_0 Int )
(declare-var main@%i.2.i.lcssa_0 Int )
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
             (= main@%j.0.i7_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%x.0.i6_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%y.0.i5_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%i.0.i4_0 0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%j.0.i7_1 main@%j.0.i7_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%x.0.i6_1 main@%x.0.i6_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%y.0.i5_1 main@%y.0.i5_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%i.0.i4_1 main@%i.0.i4_0)))
    (main@.preheader main@%x.0.i6_1
                     main@%y.0.i5_1
                     @__VERIFIER_nondet_int_0
                     main@%j.0.i7_1
                     main@%i.0.i4_1)))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_2_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%i.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%i.0.i.lcssa_1 main@%i.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_17_0 (< main@%i.0.i.lcssa_1 main@%j.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_17_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.preheader main@%x.0.i6_0
                                 main@%y.0.i5_0
                                 @__VERIFIER_nondet_int_0
                                 main@%j.0.i7_0
                                 main@%i.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) main@%_5_0)
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%j.1.i.lcssa_0 main@%j.0.i7_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%i.1.i.lcssa_0 main@%i.0.i4_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%not.1.i_0
                       (>= main@%i.1.i.lcssa_1 main@%j.1.i.lcssa_1)))
                (=> main@._crit_edge_0
                    (= main@%_13_0 (ite main@%not.1.i_0 1 0)))
                (=> main@._crit_edge_0
                    (= main@%x.1.i_0 (+ main@%_13_0 main@%x.0.i6_0)))
                (=> main@._crit_edge_0 (= main@%y.1.i_0 (+ main@%y.0.i5_0 1)))
                (=> main@._crit_edge_0 (= main@%_14_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_16_0 (= main@%_15_0 0)))
                (=> main@.preheader_1
                    (and main@.preheader_1 main@._crit_edge_0))
                main@.preheader_1
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%j.0.i7_1 main@%j.1.i.lcssa_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%x.0.i6_1 main@%x.1.i_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%y.0.i5_1 main@%y.1.i_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%i.0.i4_1 main@%i.1.i.lcssa_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%j.0.i7_2 main@%j.0.i7_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%x.0.i6_2 main@%x.0.i6_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%y.0.i5_2 main@%y.0.i5_1))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%i.0.i4_2 main@%i.0.i4_1)))))
  (=> a!1
      (main@.preheader main@%x.0.i6_2
                       main@%y.0.i5_2
                       @__VERIFIER_nondet_int_0
                       main@%j.0.i7_2
                       main@%i.0.i4_2))))
(rule (let ((a!1 (and (main@.preheader main@%x.0.i6_0
                                 main@%y.0.i5_0
                                 @__VERIFIER_nondet_int_0
                                 main@%j.0.i7_0
                                 main@%i.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (not main@%_5_0))
                (=> main@.lr.ph_0
                    (= main@%_6_0 (= main@%x.0.i6_0 main@%y.0.i5_0)))
                (=> main@.lr.ph_0 (= main@%_7_0 (ite main@%_6_0 1 0)))
                (=> main@.lr.ph_0 (= main@%not..i_0 (xor main@%_6_0 true)))
                (=> main@.lr.ph_0 (= main@%_8_0 (ite main@%not..i_0 1 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%j.1.i2_0 main@%j.0.i7_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%i.1.i1_0 main@%i.0.i4_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%j.1.i2_1 main@%j.1.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%i.1.i1_1 main@%i.1.i1_0)))))
  (=> a!1
      (main@_bb main@%x.0.i6_0
                main@%y.0.i5_0
                @__VERIFIER_nondet_int_0
                main@%i.1.i1_1
                main@%_7_0
                main@%j.1.i2_1
                main@%_8_0))))
(rule (let ((a!1 (and (main@.preheader main@%x.0.i6_0
                                 main@%y.0.i5_0
                                 @__VERIFIER_nondet_int_0
                                 main@%j.0.i7_0
                                 main@%i.0.i4_0)
                true
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) main@%_5_0)
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%j.1.i.lcssa_0 main@%j.0.i7_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%i.1.i.lcssa_0 main@%i.0.i4_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@.preheader_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%not.1.i_0
                       (>= main@%i.1.i.lcssa_1 main@%j.1.i.lcssa_1)))
                (=> main@._crit_edge_0
                    (= main@%_13_0 (ite main@%not.1.i_0 1 0)))
                (=> main@._crit_edge_0
                    (= main@%x.1.i_0 (+ main@%_13_0 main@%x.0.i6_0)))
                (=> main@._crit_edge_0 (= main@%y.1.i_0 (+ main@%y.0.i5_0 1)))
                (=> main@._crit_edge_0 (= main@%_14_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_16_0 (= main@%_15_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@._crit_edge_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    main@%_16_0)
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%i.1.i.lcssa.lcssa_0 main@%i.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%j.1.i.lcssa.lcssa_0 main@%j.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%i.1.i.lcssa.lcssa_1 main@%i.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%j.1.i.lcssa.lcssa_1 main@%j.1.i.lcssa.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%j.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_0 main@%i.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_1 main@%i.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_17_0 (< main@%i.0.i.lcssa_1 main@%j.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_17_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@_bb main@%x.0.i6_0
                          main@%y.0.i5_0
                          @__VERIFIER_nondet_int_0
                          main@%i.1.i1_0
                          main@%_7_0
                          main@%j.1.i2_0
                          main@%_8_0)
                true
                (= main@%i.2.i_0 (+ main@%i.1.i1_0 main@%_7_0))
                (= main@%j.2.i_0 (+ main@%j.1.i2_0 main@%_8_0))
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0) main@%_12_0)
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%j.2.i.lcssa_0 main@%j.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%i.2.i.lcssa_0 main@%i.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%j.2.i.lcssa_1 main@%j.2.i.lcssa_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%i.2.i.lcssa_1 main@%i.2.i.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%j.1.i.lcssa_0 main@%j.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%i.1.i.lcssa_0 main@%i.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%not.1.i_0
                       (>= main@%i.1.i.lcssa_1 main@%j.1.i.lcssa_1)))
                (=> main@._crit_edge_0
                    (= main@%_13_0 (ite main@%not.1.i_0 1 0)))
                (=> main@._crit_edge_0
                    (= main@%x.1.i_0 (+ main@%_13_0 main@%x.0.i6_0)))
                (=> main@._crit_edge_0 (= main@%y.1.i_0 (+ main@%y.0.i5_0 1)))
                (=> main@._crit_edge_0 (= main@%_14_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_16_0 (= main@%_15_0 0)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@._crit_edge_0))
                main@.preheader_0
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (not main@%_16_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%j.0.i7_0 main@%j.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%x.0.i6_1 main@%x.1.i_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%y.0.i5_1 main@%y.1.i_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%i.0.i4_0 main@%i.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%j.0.i7_1 main@%j.0.i7_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%x.0.i6_2 main@%x.0.i6_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%y.0.i5_2 main@%y.0.i5_1))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%i.0.i4_1 main@%i.0.i4_0)))))
  (=> a!1
      (main@.preheader main@%x.0.i6_2
                       main@%y.0.i5_2
                       @__VERIFIER_nondet_int_0
                       main@%j.0.i7_1
                       main@%i.0.i4_1))))
(rule (=> (and (main@_bb main@%x.0.i6_0
                   main@%y.0.i5_0
                   @__VERIFIER_nondet_int_0
                   main@%i.1.i1_0
                   main@%_7_0
                   main@%j.1.i2_0
                   main@%_8_0)
         true
         (= main@%i.2.i_0 (+ main@%i.1.i1_0 main@%_7_0))
         (= main@%j.2.i_0 (+ main@%j.1.i2_0 main@%_8_0))
         (= main@%_10_0 @__VERIFIER_nondet_int_0)
         (= main@%_12_0 (= main@%_11_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_12_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.1.i2_1 main@%j.2.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%i.1.i1_1 main@%i.2.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.1.i2_2 main@%j.1.i2_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%i.1.i1_2 main@%i.1.i1_1)))
    (main@_bb main@%x.0.i6_0
              main@%y.0.i5_0
              @__VERIFIER_nondet_int_0
              main@%i.1.i1_2
              main@%_7_0
              main@%j.1.i2_2
              main@%_8_0)))
(rule (let ((a!1 (and (main@_bb main@%x.0.i6_0
                          main@%y.0.i5_0
                          @__VERIFIER_nondet_int_0
                          main@%i.1.i1_0
                          main@%_7_0
                          main@%j.1.i2_0
                          main@%_8_0)
                true
                (= main@%i.2.i_0 (+ main@%i.1.i1_0 main@%_7_0))
                (= main@%j.2.i_0 (+ main@%j.1.i2_0 main@%_8_0))
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0) main@%_12_0)
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%j.2.i.lcssa_0 main@%j.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%i.2.i.lcssa_0 main@%i.2.i_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%j.2.i.lcssa_1 main@%j.2.i.lcssa_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb_0)
                    (= main@%i.2.i.lcssa_1 main@%i.2.i.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%j.1.i.lcssa_0 main@%j.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%i.1.i.lcssa_0 main@%i.2.i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> main@._crit_edge_0
                    (= main@%not.1.i_0
                       (>= main@%i.1.i.lcssa_1 main@%j.1.i.lcssa_1)))
                (=> main@._crit_edge_0
                    (= main@%_13_0 (ite main@%not.1.i_0 1 0)))
                (=> main@._crit_edge_0
                    (= main@%x.1.i_0 (+ main@%_13_0 main@%x.0.i6_0)))
                (=> main@._crit_edge_0 (= main@%y.1.i_0 (+ main@%y.0.i5_0 1)))
                (=> main@._crit_edge_0 (= main@%_14_0 @__VERIFIER_nondet_int_0))
                (=> main@._crit_edge_0 (= main@%_16_0 (= main@%_15_0 0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@._crit_edge_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    main@%_16_0)
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%i.1.i.lcssa.lcssa_0 main@%i.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%j.1.i.lcssa.lcssa_0 main@%j.1.i.lcssa_1))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%i.1.i.lcssa.lcssa_1 main@%i.1.i.lcssa.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@._crit_edge_0)
                    (= main@%j.1.i.lcssa.lcssa_1 main@%j.1.i.lcssa.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%j.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_0 main@%i.1.i.lcssa.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_1 main@%i.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_17_0 (< main@%i.0.i.lcssa_1 main@%j.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_17_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

