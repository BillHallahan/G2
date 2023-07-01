(set-info :original "/tmp/sea-SFpTnP/29.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph9 (Int Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_22_0 Bool )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%.lcssa31_1 Int )
(declare-var main@%.lcssa30_1 Int )
(declare-var main@%_19_0 Int )
(declare-var main@%_20_0 Int )
(declare-var main@%_21_0 Bool )
(declare-var main@%.lcssa29_1 Int )
(declare-var main@%.lcssa28_1 Int )
(declare-var main@%b.1.i3_2 Int )
(declare-var main@%c.1.i2_2 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%a.1.v.i_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%_16_0 Bool )
(declare-var main@%_8_2 Int )
(declare-var main@%_9_2 Int )
(declare-var main@%a.0.i8_2 Int )
(declare-var main@%d.0.i5_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@.lr.ph9.preheader_0 Bool )
(declare-var main@.lr.ph9_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%a.0.i8_0 Int )
(declare-var main@%b.0.i7_0 Int )
(declare-var main@%c.0.i6_0 Int )
(declare-var main@%d.0.i5_0 Int )
(declare-var main@%_8_1 Int )
(declare-var main@%_9_1 Int )
(declare-var main@%a.0.i8_1 Int )
(declare-var main@%b.0.i7_1 Int )
(declare-var main@%c.0.i6_1 Int )
(declare-var main@%d.0.i5_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%.lcssa1_0 Int )
(declare-var main@%.lcssa_0 Int )
(declare-var main@%.lcssa1_1 Int )
(declare-var main@%.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%d.1.i_0 Int )
(declare-var main@%a.1.i_0 Int )
(declare-var main@.loopexit_0 Bool )
(declare-var main@%b.1.i.lcssa_0 Int )
(declare-var main@%c.1.i.lcssa_0 Int )
(declare-var main@%b.1.i.lcssa_1 Int )
(declare-var main@%c.1.i.lcssa_1 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@.lr.ph9_1 Bool )
(declare-var main@%b.0.i7_2 Int )
(declare-var main@%c.0.i6_2 Int )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%b.1.i3_0 Int )
(declare-var main@%c.1.i2_0 Int )
(declare-var main@%b.1.i3_1 Int )
(declare-var main@%c.1.i2_1 Int )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%.lcssa31_0 Int )
(declare-var main@%.lcssa30_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@.loopexit.loopexit_0 Bool )
(declare-var main@%.lcssa29_0 Int )
(declare-var main@%.lcssa28_0 Int )
(declare-var main@.lr.ph_1 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 (= main@%_1_0 0))
         (=> main@.lr.ph9.preheader_0
             (and main@.lr.ph9.preheader_0 main@entry_0))
         (=> (and main@.lr.ph9.preheader_0 main@entry_0) (not main@%_2_0))
         (=> main@.lr.ph9_0 (and main@.lr.ph9_0 main@.lr.ph9.preheader_0))
         main@.lr.ph9_0
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%_8_0 3))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%_9_0 3))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%a.0.i8_0 1))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%b.0.i7_0 1))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%c.0.i6_0 2))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0) (= main@%d.0.i5_0 2))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%_8_1 main@%_8_0))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%_9_1 main@%_9_0))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%a.0.i8_1 main@%a.0.i8_0))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%b.0.i7_1 main@%b.0.i7_0))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%c.0.i6_1 main@%c.0.i6_0))
         (=> (and main@.lr.ph9_0 main@.lr.ph9.preheader_0)
             (= main@%d.0.i5_1 main@%d.0.i5_0)))
    (main@.lr.ph9 @__VERIFIER_nondet_int_0
                  main@%_8_1
                  main@%_9_1
                  main@%a.0.i8_1
                  main@%b.0.i7_1
                  main@%c.0.i6_1
                  main@%d.0.i5_1)))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 (= main@%_1_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_2_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.lcssa1_0 3))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.lcssa_0 3))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.lcssa1_1 main@%.lcssa1_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.lcssa_1 main@%.lcssa1_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.lr.ph9 @__VERIFIER_nondet_int_0
                              main@%_8_0
                              main@%_9_0
                              main@%a.0.i8_0
                              main@%b.0.i7_0
                              main@%c.0.i6_0
                              main@%d.0.i5_0)
                true
                (= main@%_10_0 (+ main@%_9_0 main@%_8_0))
                (= main@%_11_0 (rem main@%_10_0 2))
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%_13_0 (ite main@%_12_0 1 0))
                (= main@%d.1.i_0 (+ main@%_13_0 main@%d.0.i5_0))
                (= main@%a.1.v.i_0 (ite main@%_12_0 1 (- 1)))
                (= main@%a.1.i_0 (+ main@%a.1.v.i_0 main@%a.0.i8_0))
                (= main@%_14_0 @__VERIFIER_nondet_int_0)
                (= main@%_16_0 (= main@%_15_0 0))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.lr.ph9_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0) main@%_16_0)
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%b.1.i.lcssa_0 main@%b.0.i7_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%c.1.i.lcssa_0 main@%c.0.i6_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%b.1.i.lcssa_1 main@%b.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%c.1.i.lcssa_1 main@%c.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_3_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_5_0 (= main@%_4_0 0)))
                (=> main@.loopexit_0
                    (= main@%_6_0 (+ main@%a.1.i_0 main@%c.1.i.lcssa_1)))
                (=> main@.loopexit_0
                    (= main@%_7_0 (+ main@%b.1.i.lcssa_1 main@%d.1.i_0)))
                (=> main@.lr.ph9_1 (and main@.lr.ph9_1 main@.loopexit_0))
                main@.lr.ph9_1
                (=> (and main@.lr.ph9_1 main@.loopexit_0) (not main@%_5_0))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%_8_1 main@%_7_0))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%_9_1 main@%_6_0))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%a.0.i8_1 main@%a.1.i_0))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%b.0.i7_1 main@%b.1.i.lcssa_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%c.0.i6_1 main@%c.1.i.lcssa_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%d.0.i5_1 main@%d.1.i_0))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%_8_2 main@%_8_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%_9_2 main@%_9_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%a.0.i8_2 main@%a.0.i8_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%b.0.i7_2 main@%b.0.i7_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%c.0.i6_2 main@%c.0.i6_1))
                (=> (and main@.lr.ph9_1 main@.loopexit_0)
                    (= main@%d.0.i5_2 main@%d.0.i5_1)))))
  (=> a!1
      (main@.lr.ph9 @__VERIFIER_nondet_int_0
                    main@%_8_2
                    main@%_9_2
                    main@%a.0.i8_2
                    main@%b.0.i7_2
                    main@%c.0.i6_2
                    main@%d.0.i5_2))))
(rule (=> (and (main@.lr.ph9 @__VERIFIER_nondet_int_0
                       main@%_8_0
                       main@%_9_0
                       main@%a.0.i8_0
                       main@%b.0.i7_0
                       main@%c.0.i6_0
                       main@%d.0.i5_0)
         true
         (= main@%_10_0 (+ main@%_9_0 main@%_8_0))
         (= main@%_11_0 (rem main@%_10_0 2))
         (= main@%_12_0 (= main@%_11_0 0))
         (= main@%_13_0 (ite main@%_12_0 1 0))
         (= main@%d.1.i_0 (+ main@%_13_0 main@%d.0.i5_0))
         (= main@%a.1.v.i_0 (ite main@%_12_0 1 (- 1)))
         (= main@%a.1.i_0 (+ main@%a.1.v.i_0 main@%a.0.i8_0))
         (= main@%_14_0 @__VERIFIER_nondet_int_0)
         (= main@%_16_0 (= main@%_15_0 0))
         (=> main@.lr.ph.preheader_0
             (and main@.lr.ph.preheader_0 main@.lr.ph9_0))
         (=> (and main@.lr.ph.preheader_0 main@.lr.ph9_0) (not main@%_16_0))
         (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
         main@.lr.ph_0
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%b.1.i3_0 main@%b.0.i7_0))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%c.1.i2_0 main@%c.0.i6_0))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%b.1.i3_1 main@%b.1.i3_0))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%c.1.i2_1 main@%c.1.i2_0)))
    (main@.lr.ph @__VERIFIER_nondet_int_0
                 main@%a.1.i_0
                 main@%d.1.i_0
                 main@%c.1.i2_1
                 main@%b.1.i3_1)))
(rule (let ((a!1 (and (main@.lr.ph9 @__VERIFIER_nondet_int_0
                              main@%_8_0
                              main@%_9_0
                              main@%a.0.i8_0
                              main@%b.0.i7_0
                              main@%c.0.i6_0
                              main@%d.0.i5_0)
                true
                (= main@%_10_0 (+ main@%_9_0 main@%_8_0))
                (= main@%_11_0 (rem main@%_10_0 2))
                (= main@%_12_0 (= main@%_11_0 0))
                (= main@%_13_0 (ite main@%_12_0 1 0))
                (= main@%d.1.i_0 (+ main@%_13_0 main@%d.0.i5_0))
                (= main@%a.1.v.i_0 (ite main@%_12_0 1 (- 1)))
                (= main@%a.1.i_0 (+ main@%a.1.v.i_0 main@%a.0.i8_0))
                (= main@%_14_0 @__VERIFIER_nondet_int_0)
                (= main@%_16_0 (= main@%_15_0 0))
                (=> main@.loopexit_0 (and main@.loopexit_0 main@.lr.ph9_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0) main@%_16_0)
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%b.1.i.lcssa_0 main@%b.0.i7_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%c.1.i.lcssa_0 main@%c.0.i6_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%b.1.i.lcssa_1 main@%b.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.lr.ph9_0)
                    (= main@%c.1.i.lcssa_1 main@%c.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_3_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_5_0 (= main@%_4_0 0)))
                (=> main@.loopexit_0
                    (= main@%_6_0 (+ main@%a.1.i_0 main@%c.1.i.lcssa_1)))
                (=> main@.loopexit_0
                    (= main@%_7_0 (+ main@%b.1.i.lcssa_1 main@%d.1.i_0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.loopexit_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    main@%_5_0)
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa31_0 main@%_7_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa30_0 main@%_6_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa31_1 main@%.lcssa31_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa30_1 main@%.lcssa30_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa1_0 main@%.lcssa31_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa_0 main@%.lcssa30_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa1_1 main@%.lcssa1_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.lcssa_1 main@%.lcssa1_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (let ((a!1 (and (main@.lr.ph @__VERIFIER_nondet_int_0
                             main@%a.1.i_0
                             main@%d.1.i_0
                             main@%c.1.i2_0
                             main@%b.1.i3_0)
                true
                (= main@%_17_0 (+ main@%c.1.i2_0 (- 1)))
                (= main@%_18_0 (+ main@%b.1.i3_0 (- 1)))
                (= main@%_19_0 @__VERIFIER_nondet_int_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@.loopexit.loopexit_0
                    (and main@.loopexit.loopexit_0 main@.lr.ph_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0) main@%_21_0)
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa29_0 main@%_18_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa28_0 main@%_17_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa29_1 main@%.lcssa29_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa28_1 main@%.lcssa28_0))
                (=> main@.loopexit_0
                    (and main@.loopexit_0 main@.loopexit.loopexit_0))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%b.1.i.lcssa_0 main@%.lcssa29_1))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%c.1.i.lcssa_0 main@%.lcssa28_1))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%b.1.i.lcssa_1 main@%b.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%c.1.i.lcssa_1 main@%c.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_3_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_5_0 (= main@%_4_0 0)))
                (=> main@.loopexit_0
                    (= main@%_6_0 (+ main@%a.1.i_0 main@%c.1.i.lcssa_1)))
                (=> main@.loopexit_0
                    (= main@%_7_0 (+ main@%b.1.i.lcssa_1 main@%d.1.i_0)))
                (=> main@.lr.ph9_0 (and main@.lr.ph9_0 main@.loopexit_0))
                main@.lr.ph9_0
                (=> (and main@.lr.ph9_0 main@.loopexit_0) (not main@%_5_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%_8_0 main@%_7_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%_9_0 main@%_6_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%a.0.i8_0 main@%a.1.i_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%b.0.i7_0 main@%b.1.i.lcssa_1))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%c.0.i6_0 main@%c.1.i.lcssa_1))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%d.0.i5_0 main@%d.1.i_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%_8_1 main@%_8_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%_9_1 main@%_9_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%a.0.i8_1 main@%a.0.i8_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%b.0.i7_1 main@%b.0.i7_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%c.0.i6_1 main@%c.0.i6_0))
                (=> (and main@.lr.ph9_0 main@.loopexit_0)
                    (= main@%d.0.i5_1 main@%d.0.i5_0)))))
  (=> a!1
      (main@.lr.ph9 @__VERIFIER_nondet_int_0
                    main@%_8_1
                    main@%_9_1
                    main@%a.0.i8_1
                    main@%b.0.i7_1
                    main@%c.0.i6_1
                    main@%d.0.i5_1))))
(rule (=> (and (main@.lr.ph @__VERIFIER_nondet_int_0
                      main@%a.1.i_0
                      main@%d.1.i_0
                      main@%c.1.i2_0
                      main@%b.1.i3_0)
         true
         (= main@%_17_0 (+ main@%c.1.i2_0 (- 1)))
         (= main@%_18_0 (+ main@%b.1.i3_0 (- 1)))
         (= main@%_19_0 @__VERIFIER_nondet_int_0)
         (= main@%_21_0 (= main@%_20_0 0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         main@.lr.ph_1
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (not main@%_21_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%b.1.i3_1 main@%_18_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%c.1.i2_1 main@%_17_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%b.1.i3_2 main@%b.1.i3_1))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%c.1.i2_2 main@%c.1.i2_1)))
    (main@.lr.ph @__VERIFIER_nondet_int_0
                 main@%a.1.i_0
                 main@%d.1.i_0
                 main@%c.1.i2_2
                 main@%b.1.i3_2)))
(rule (let ((a!1 (and (main@.lr.ph @__VERIFIER_nondet_int_0
                             main@%a.1.i_0
                             main@%d.1.i_0
                             main@%c.1.i2_0
                             main@%b.1.i3_0)
                true
                (= main@%_17_0 (+ main@%c.1.i2_0 (- 1)))
                (= main@%_18_0 (+ main@%b.1.i3_0 (- 1)))
                (= main@%_19_0 @__VERIFIER_nondet_int_0)
                (= main@%_21_0 (= main@%_20_0 0))
                (=> main@.loopexit.loopexit_0
                    (and main@.loopexit.loopexit_0 main@.lr.ph_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0) main@%_21_0)
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa29_0 main@%_18_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa28_0 main@%_17_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa29_1 main@%.lcssa29_0))
                (=> (and main@.loopexit.loopexit_0 main@.lr.ph_0)
                    (= main@%.lcssa28_1 main@%.lcssa28_0))
                (=> main@.loopexit_0
                    (and main@.loopexit_0 main@.loopexit.loopexit_0))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%b.1.i.lcssa_0 main@%.lcssa29_1))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%c.1.i.lcssa_0 main@%.lcssa28_1))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%b.1.i.lcssa_1 main@%b.1.i.lcssa_0))
                (=> (and main@.loopexit_0 main@.loopexit.loopexit_0)
                    (= main@%c.1.i.lcssa_1 main@%c.1.i.lcssa_0))
                (=> main@.loopexit_0 (= main@%_3_0 @__VERIFIER_nondet_int_0))
                (=> main@.loopexit_0 (= main@%_5_0 (= main@%_4_0 0)))
                (=> main@.loopexit_0
                    (= main@%_6_0 (+ main@%a.1.i_0 main@%c.1.i.lcssa_1)))
                (=> main@.loopexit_0
                    (= main@%_7_0 (+ main@%b.1.i.lcssa_1 main@%d.1.i_0)))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.loopexit_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    main@%_5_0)
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa31_0 main@%_7_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa30_0 main@%_6_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa31_1 main@%.lcssa31_0))
                (=> (and main@verifier.error.loopexit_0 main@.loopexit_0)
                    (= main@%.lcssa30_1 main@%.lcssa30_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa1_0 main@%.lcssa31_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa_0 main@%.lcssa30_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa1_1 main@%.lcssa1_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_22_0 (= main@%.lcssa_1 main@%.lcssa1_1)))
                (=> main@verifier.error_0 (not main@%_22_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

