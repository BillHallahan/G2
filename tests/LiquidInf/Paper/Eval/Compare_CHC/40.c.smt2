(set-info :original "/tmp/sea-UHXGR3/40.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph6 (Bool Int Int Int ))
(declare-rel main@_bb (Bool Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_22_0 Bool )
(declare-var main@%or.cond.i_0 Bool )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%.lcssa17_1 Int )
(declare-var main@%.lcssa_1 Int )
(declare-var main@%b.0.i2_2 Int )
(declare-var main@%a.0.i1_2 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%j.1.v.i_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Bool )
(declare-var main@%j.1.i.lcssa_1 Int )
(declare-var main@%.lcssa18_1 Int )
(declare-var main@%i.1.i5_2 Int )
(declare-var main@%j.0.i4_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_2_0 Bool )
(declare-var main@%..i_0 Int )
(declare-var main@.lr.ph6.preheader_0 Bool )
(declare-var main@.lr.ph6_0 Bool )
(declare-var main@%i.1.i5_0 Int )
(declare-var main@%j.0.i4_0 Int )
(declare-var main@%i.1.i5_1 Int )
(declare-var main@%j.0.i4_1 Int )
(declare-var main@.preheader_0 Bool )
(declare-var main@%i.1.i.lcssa_0 Int )
(declare-var main@%j.0.i.lcssa_0 Int )
(declare-var main@%i.1.i.lcssa_1 Int )
(declare-var main@%j.0.i.lcssa_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%b.0.i2_0 Int )
(declare-var main@%a.0.i1_0 Int )
(declare-var main@%b.0.i2_1 Int )
(declare-var main@%a.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%b.0.i.lcssa_0 Int )
(declare-var main@%a.0.i.lcssa_0 Int )
(declare-var main@%b.0.i.lcssa_1 Int )
(declare-var main@%a.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%j.1.i_0 Int )
(declare-var main@.lr.ph6_1 Bool )
(declare-var main@.preheader.loopexit_0 Bool )
(declare-var main@%j.1.i.lcssa_0 Int )
(declare-var main@%.lcssa18_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%.lcssa17_0 Int )
(declare-var main@%.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (= main@%..i_0 (ite main@%_2_0 1 0))
         (= main@%_3_0 @__VERIFIER_nondet_int_0)
         (= main@%_5_0 (= main@%_4_0 0))
         (=> main@.lr.ph6.preheader_0
             (and main@.lr.ph6.preheader_0 main@entry_0))
         (=> (and main@.lr.ph6.preheader_0 main@entry_0) (not main@%_5_0))
         (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@.lr.ph6.preheader_0))
         main@.lr.ph6_0
         (=> (and main@.lr.ph6_0 main@.lr.ph6.preheader_0)
             (= main@%i.1.i5_0 main@%..i_0))
         (=> (and main@.lr.ph6_0 main@.lr.ph6.preheader_0) (= main@%j.0.i4_0 1))
         (=> (and main@.lr.ph6_0 main@.lr.ph6.preheader_0)
             (= main@%i.1.i5_1 main@%i.1.i5_0))
         (=> (and main@.lr.ph6_0 main@.lr.ph6.preheader_0)
             (= main@%j.0.i4_1 main@%j.0.i4_0)))
    (main@.lr.ph6 main@%_2_0
                  @__VERIFIER_nondet_int_0
                  main@%i.1.i5_1
                  main@%j.0.i4_1)))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (= main@%..i_0 (ite main@%_2_0 1 0))
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) main@%_5_0)
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%i.1.i.lcssa_0 main@%..i_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%j.0.i.lcssa_0 1))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_6_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_8_0 (= main@%_7_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (not main@%_8_0))
                (=> main@.lr.ph_0
                    (= main@%_9_0 (- main@%j.0.i.lcssa_1 main@%i.1.i.lcssa_1)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%b.0.i2_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%a.0.i1_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%b.0.i2_1 main@%b.0.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%a.0.i1_1 main@%a.0.i1_0)))))
  (=> a!1
      (main@_bb main@%_2_0
                main@%a.0.i1_1
                main@%_9_0
                main@%b.0.i2_1
                @__VERIFIER_nondet_int_0))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (= main@%..i_0 (ite main@%_2_0 1 0))
                (= main@%_3_0 @__VERIFIER_nondet_int_0)
                (= main@%_5_0 (= main@%_4_0 0))
                (=> main@.preheader_0 (and main@.preheader_0 main@entry_0))
                (=> (and main@.preheader_0 main@entry_0) main@%_5_0)
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%i.1.i.lcssa_0 main@%..i_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%j.0.i.lcssa_0 1))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@entry_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_6_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_8_0 (= main@%_7_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0) main@%_8_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%b.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%a.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%b.0.i.lcssa_1 main@%b.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%a.0.i.lcssa_1 main@%a.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%a.0.i.lcssa_1 main@%b.0.i.lcssa_1)))
                (=> main@verifier.error_0
                    (= main@%or.cond.i_0 (or main@%_2_0 main@%_22_0)))
                (=> main@verifier.error_0 (not main@%or.cond.i_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph6 main@%_2_0
                       @__VERIFIER_nondet_int_0
                       main@%i.1.i5_0
                       main@%j.0.i4_0)
         true
         (= main@%_10_0 (+ main@%i.1.i5_0 2))
         (= main@%_11_0 (rem main@%_10_0 2))
         (= main@%_12_0 (= main@%_11_0 0))
         (= main@%j.1.v.i_0 (ite main@%_12_0 2 1))
         (= main@%j.1.i_0 (+ main@%j.1.v.i_0 main@%j.0.i4_0))
         (= main@%_13_0 @__VERIFIER_nondet_int_0)
         (= main@%_15_0 (= main@%_14_0 0))
         (=> main@.lr.ph6_1 (and main@.lr.ph6_1 main@.lr.ph6_0))
         main@.lr.ph6_1
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (not main@%_15_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0) (= main@%i.1.i5_1 main@%_10_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%j.0.i4_1 main@%j.1.i_0))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%i.1.i5_2 main@%i.1.i5_1))
         (=> (and main@.lr.ph6_1 main@.lr.ph6_0)
             (= main@%j.0.i4_2 main@%j.0.i4_1)))
    (main@.lr.ph6 main@%_2_0
                  @__VERIFIER_nondet_int_0
                  main@%i.1.i5_2
                  main@%j.0.i4_2)))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_2_0
                              @__VERIFIER_nondet_int_0
                              main@%i.1.i5_0
                              main@%j.0.i4_0)
                true
                (= main@%_10_0 (+ main@%i.1.i5_0 2))
                (= main@%_11_0 (rem main@%_10_0 2))
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%j.1.v.i_0 (ite main@%_12_0 2 1))
                (= main@%j.1.i_0 (+ main@%j.1.v.i_0 main@%j.0.i4_0))
                (= main@%_13_0 @__VERIFIER_nondet_int_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (=> main@.preheader.loopexit_0
                    (and main@.preheader.loopexit_0 main@.lr.ph6_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0) main@%_15_0)
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%j.1.i.lcssa_0 main@%j.1.i_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%.lcssa18_0 main@%_10_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%.lcssa18_1 main@%.lcssa18_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader.loopexit_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%i.1.i.lcssa_0 main@%.lcssa18_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%j.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_6_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_8_0 (= main@%_7_0 0)))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.preheader_0))
                (=> (and main@.lr.ph_0 main@.preheader_0) (not main@%_8_0))
                (=> main@.lr.ph_0
                    (= main@%_9_0 (- main@%j.0.i.lcssa_1 main@%i.1.i.lcssa_1)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%b.0.i2_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%a.0.i1_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%b.0.i2_1 main@%b.0.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%a.0.i1_1 main@%a.0.i1_0)))))
  (=> a!1
      (main@_bb main@%_2_0
                main@%a.0.i1_1
                main@%_9_0
                main@%b.0.i2_1
                @__VERIFIER_nondet_int_0))))
(rule (let ((a!1 (and (main@.lr.ph6 main@%_2_0
                              @__VERIFIER_nondet_int_0
                              main@%i.1.i5_0
                              main@%j.0.i4_0)
                true
                (= main@%_10_0 (+ main@%i.1.i5_0 2))
                (= main@%_11_0 (rem main@%_10_0 2))
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%j.1.v.i_0 (ite main@%_12_0 2 1))
                (= main@%j.1.i_0 (+ main@%j.1.v.i_0 main@%j.0.i4_0))
                (= main@%_13_0 @__VERIFIER_nondet_int_0)
                (= main@%_15_0 (= main@%_14_0 0))
                (=> main@.preheader.loopexit_0
                    (and main@.preheader.loopexit_0 main@.lr.ph6_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0) main@%_15_0)
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%j.1.i.lcssa_0 main@%j.1.i_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%.lcssa18_0 main@%_10_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> (and main@.preheader.loopexit_0 main@.lr.ph6_0)
                    (= main@%.lcssa18_1 main@%.lcssa18_0))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@.preheader.loopexit_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%i.1.i.lcssa_0 main@%.lcssa18_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%j.1.i.lcssa_1))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%i.1.i.lcssa_1 main@%i.1.i.lcssa_0))
                (=> (and main@.preheader_0 main@.preheader.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@.preheader_0 (= main@%_6_0 @__VERIFIER_nondet_int_0))
                (=> main@.preheader_0 (= main@%_8_0 (= main@%_7_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@.preheader_0))
                (=> (and main@verifier.error_0 main@.preheader_0) main@%_8_0)
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%b.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%a.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%b.0.i.lcssa_1 main@%b.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@.preheader_0)
                    (= main@%a.0.i.lcssa_1 main@%a.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%a.0.i.lcssa_1 main@%b.0.i.lcssa_1)))
                (=> main@verifier.error_0
                    (= main@%or.cond.i_0 (or main@%_2_0 main@%_22_0)))
                (=> main@verifier.error_0 (not main@%or.cond.i_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@_bb main@%_2_0
                   main@%a.0.i1_0
                   main@%_9_0
                   main@%b.0.i2_0
                   @__VERIFIER_nondet_int_0)
         true
         (= main@%_17_0 (+ main@%a.0.i1_0 1))
         (= main@%_18_0 (+ main@%_9_0 main@%b.0.i2_0))
         (= main@%_19_0 @__VERIFIER_nondet_int_0)
         (= main@%_21_0 (= main@%_20_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_21_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%b.0.i2_1 main@%_18_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%a.0.i1_1 main@%_17_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%b.0.i2_2 main@%b.0.i2_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%a.0.i1_2 main@%a.0.i1_1)))
    (main@_bb main@%_2_0
              main@%a.0.i1_2
              main@%_9_0
              main@%b.0.i2_2
              @__VERIFIER_nondet_int_0)))
(rule (let ((a!1 (and (main@_bb main@%_2_0
                          main@%a.0.i1_0
                          main@%_9_0
                          main@%b.0.i2_0
                          @__VERIFIER_nondet_int_0)
                true
                (= main@%_17_0 (+ main@%a.0.i1_0 1))
                (= main@%_18_0 (+ main@%_9_0 main@%b.0.i2_0))
                (= main@%_19_0 @__VERIFIER_nondet_int_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@_bb_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0) main@%_21_0)
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa17_0 main@%_18_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa_0 main@%_17_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa17_1 main@%.lcssa17_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%b.0.i.lcssa_0 main@%.lcssa17_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%a.0.i.lcssa_0 main@%.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%b.0.i.lcssa_1 main@%b.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%a.0.i.lcssa_1 main@%a.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%a.0.i.lcssa_1 main@%b.0.i.lcssa_1)))
                (=> main@verifier.error_0
                    (= main@%or.cond.i_0 (or main@%_2_0 main@%_22_0)))
                (=> main@verifier.error_0 (not main@%or.cond.i_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

