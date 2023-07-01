(set-info :original "/tmp/sea-rlkB4U/12.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@.lr.ph6.split (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph6.split.us (Int Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_26_0 Int )
(declare-var main@%_27_0 Int )
(declare-var main@%_28_0 Bool )
(declare-var main@%y.1.v.i_0 Int )
(declare-var main@%_29_0 Bool )
(declare-var main@%y.1.i.lcssa_1 Int )
(declare-var main@%y.0.i1_2 Int )
(declare-var main@%_22_0 Int )
(declare-var main@%_23_0 Int )
(declare-var main@%_25_0 Bool )
(declare-var main@%_20_0 Bool )
(declare-var main@%x.0.i12_2 Int )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%.lcssa22_1 Int )
(declare-var main@%.lcssa_1 Int )
(declare-var main@%t.0.i5.us_2 Int )
(declare-var main@%s.0.i4.us_2 Int )
(declare-var main@%a.0.i3.us_2 Int )
(declare-var main@%b.0.i2.us_2 Int )
(declare-var main@%_16_0 Int )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Int )
(declare-var main@%_19_0 Bool )
(declare-var main@%..i.lcssa_1 Int )
(declare-var main@%.lcssa23_1 Int )
(declare-var main@%t.0.i5_2 Int )
(declare-var main@%s.0.i4_2 Int )
(declare-var main@%a.0.i3_2 Int )
(declare-var main@%b.0.i2_2 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@.lr.ph6_0 Bool )
(declare-var main@.lr.ph6.split.preheader_0 Bool )
(declare-var main@.lr.ph6.split_0 Bool )
(declare-var main@%t.0.i5_0 Int )
(declare-var main@%s.0.i4_0 Int )
(declare-var main@%a.0.i3_0 Int )
(declare-var main@%b.0.i2_0 Int )
(declare-var main@%t.0.i5_1 Int )
(declare-var main@%s.0.i4_1 Int )
(declare-var main@%a.0.i3_1 Int )
(declare-var main@%b.0.i2_1 Int )
(declare-var main@.lr.ph6.split.us.preheader_0 Bool )
(declare-var main@.lr.ph6.split.us_0 Bool )
(declare-var main@%t.0.i5.us_0 Int )
(declare-var main@%s.0.i4.us_0 Int )
(declare-var main@%a.0.i3.us_0 Int )
(declare-var main@%b.0.i2.us_0 Int )
(declare-var main@%t.0.i5.us_1 Int )
(declare-var main@%s.0.i4.us_1 Int )
(declare-var main@%a.0.i3.us_1 Int )
(declare-var main@%b.0.i2.us_1 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%t.0.i.lcssa_0 Int )
(declare-var main@%s.0.i.lcssa_0 Int )
(declare-var main@%t.0.i.lcssa_1 Int )
(declare-var main@%s.0.i.lcssa_1 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%_24_0 Int )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)| Bool )
(declare-var |tuple(main@_bb_0, main@.lr.ph.preheader_0)| Bool )
(declare-var main@%x.0.i12_0 Int )
(declare-var main@%x.0.i12_1 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%y.0.i1_0 Int )
(declare-var main@%y.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%y.0.i.lcssa_0 Bool )
(declare-var main@%y.0.i.lcssa_1 Bool )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Int )
(declare-var main@%_15_0 Int )
(declare-var main@%..i_0 Int )
(declare-var main@.lr.ph6.split_1 Bool )
(declare-var main@._crit_edge.loopexit19_0 Bool )
(declare-var main@%..i.lcssa_0 Int )
(declare-var main@%.lcssa23_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@.lr.ph6.split.us_1 Bool )
(declare-var main@._crit_edge.loopexit_0 Bool )
(declare-var main@%.lcssa22_0 Int )
(declare-var main@%.lcssa_0 Int )
(declare-var main@%y.1.i_0 Int )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%y.1.i.lcssa_0 Int )
(declare-var main@%phitmp_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
                (=> (and main@.lr.ph6_0 main@entry_0) (not main@%_4_0))
                (=> main@.lr.ph6_0 (= main@%_5_0 (= main@%_1_0 0)))
                (=> main@.lr.ph6.split.preheader_0
                    (and main@.lr.ph6.split.preheader_0 main@.lr.ph6_0))
                (=> (and main@.lr.ph6.split.preheader_0 main@.lr.ph6_0)
                    (not main@%_5_0))
                (=> main@.lr.ph6.split_0
                    (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0))
                main@.lr.ph6.split_0
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%t.0.i5_0 0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%s.0.i4_0 0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%a.0.i3_0 0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%b.0.i2_0 0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%t.0.i5_1 main@%t.0.i5_0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%s.0.i4_1 main@%s.0.i4_0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%a.0.i3_1 main@%a.0.i3_0))
                (=> (and main@.lr.ph6.split_0 main@.lr.ph6.split.preheader_0)
                    (= main@%b.0.i2_1 main@%b.0.i2_0)))))
  (=> a!1
      (main@.lr.ph6.split
        @__VERIFIER_nondet_int_0
        main@%_1_0
        main@%a.0.i3_1
        main@%b.0.i2_1
        main@%s.0.i4_1
        main@%t.0.i5_1))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@.lr.ph6_0 (and main@.lr.ph6_0 main@entry_0))
                (=> (and main@.lr.ph6_0 main@entry_0) (not main@%_4_0))
                (=> main@.lr.ph6_0 (= main@%_5_0 (= main@%_1_0 0)))
                (=> main@.lr.ph6.split.us.preheader_0
                    (and main@.lr.ph6.split.us.preheader_0 main@.lr.ph6_0))
                (=> (and main@.lr.ph6.split.us.preheader_0 main@.lr.ph6_0)
                    main@%_5_0)
                (=> main@.lr.ph6.split.us_0
                    (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0))
                main@.lr.ph6.split.us_0
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%t.0.i5.us_0 0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%s.0.i4.us_0 0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%a.0.i3.us_0 0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%b.0.i2.us_0 0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%t.0.i5.us_1 main@%t.0.i5.us_0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%s.0.i4.us_1 main@%s.0.i4.us_0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%a.0.i3.us_1 main@%a.0.i3.us_0))
                (=> (and main@.lr.ph6.split.us_0
                         main@.lr.ph6.split.us.preheader_0)
                    (= main@%b.0.i2.us_1 main@%b.0.i2.us_0)))))
  (=> a!1
      (main@.lr.ph6.split.us
        @__VERIFIER_nondet_int_0
        main@%_1_0
        main@%a.0.i3.us_1
        main@%b.0.i2.us_1
        main@%s.0.i4.us_1
        main@%t.0.i5.us_1))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@entry_0))
                (=> (and main@._crit_edge_0 main@entry_0) main@%_4_0)
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%t.0.i.lcssa_0 0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%s.0.i.lcssa_0 0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|
                    main@._crit_edge_0)
                (=> |tuple(main@_bb_0, main@.lr.ph.preheader_0)| main@_bb_0)
                (=> main@.lr.ph.preheader_0
                    (or (and main@._crit_edge_0
                             |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                        (and main@_bb_0
                             |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    main@%_20_0)
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_0 1))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (not main@%_25_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_1 main@%_24_0))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_1))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
                main@.lr.ph_0
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_0 0))
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_1 main@%y.0.i1_0)))))
  (=> a!1 (main@.lr.ph @__VERIFIER_nondet_int_0 main@%y.0.i1_1 main@%x.0.i12_2))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@entry_0))
                (=> (and main@._crit_edge_0 main@entry_0) main@%_4_0)
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%t.0.i.lcssa_0 0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%s.0.i.lcssa_0 0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@entry_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_bb_0))
                (=> (and main@verifier.error_0 main@_bb_0) main@%_25_0)
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_0 true))
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0 (not main@%y.0.i.lcssa_1))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph6.split
           @__VERIFIER_nondet_int_0
           main@%_1_0
           main@%a.0.i3_0
           main@%b.0.i2_0
           main@%s.0.i4_0
           main@%t.0.i5_0)
         true
         (= main@%_13_0 (+ main@%a.0.i3_0 1))
         (= main@%_14_0 (+ main@%b.0.i2_0 1))
         (= main@%_15_0 (+ main@%s.0.i4_0 main@%_13_0))
         (= main@%_16_0 (+ main@%t.0.i5_0 main@%_14_0))
         (= main@%..i_0 (+ main@%_16_0 main@%_13_0))
         (= main@%_17_0 @__VERIFIER_nondet_int_0)
         (= main@%_19_0 (= main@%_18_0 0))
         (=> main@.lr.ph6.split_1
             (and main@.lr.ph6.split_1 main@.lr.ph6.split_0))
         main@.lr.ph6.split_1
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0) (not main@%_19_0))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%t.0.i5_1 main@%..i_0))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%s.0.i4_1 main@%_15_0))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%a.0.i3_1 main@%_13_0))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%b.0.i2_1 main@%_14_0))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%t.0.i5_2 main@%t.0.i5_1))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%s.0.i4_2 main@%s.0.i4_1))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%a.0.i3_2 main@%a.0.i3_1))
         (=> (and main@.lr.ph6.split_1 main@.lr.ph6.split_0)
             (= main@%b.0.i2_2 main@%b.0.i2_1)))
    (main@.lr.ph6.split
      @__VERIFIER_nondet_int_0
      main@%_1_0
      main@%a.0.i3_2
      main@%b.0.i2_2
      main@%s.0.i4_2
      main@%t.0.i5_2)))
(rule (let ((a!1 (and (main@.lr.ph6.split
                  @__VERIFIER_nondet_int_0
                  main@%_1_0
                  main@%a.0.i3_0
                  main@%b.0.i2_0
                  main@%s.0.i4_0
                  main@%t.0.i5_0)
                true
                (= main@%_13_0 (+ main@%a.0.i3_0 1))
                (= main@%_14_0 (+ main@%b.0.i2_0 1))
                (= main@%_15_0 (+ main@%s.0.i4_0 main@%_13_0))
                (= main@%_16_0 (+ main@%t.0.i5_0 main@%_14_0))
                (= main@%..i_0 (+ main@%_16_0 main@%_13_0))
                (= main@%_17_0 @__VERIFIER_nondet_int_0)
                (= main@%_19_0 (= main@%_18_0 0))
                (=> main@._crit_edge.loopexit19_0
                    (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    main@%_19_0)
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%..i.lcssa_0 main@%..i_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%.lcssa23_0 main@%_15_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%..i.lcssa_1 main@%..i.lcssa_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%.lcssa23_1 main@%.lcssa23_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit19_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%t.0.i.lcssa_0 main@%..i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%s.0.i.lcssa_0 main@%.lcssa23_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|
                    main@._crit_edge_0)
                (=> |tuple(main@_bb_0, main@.lr.ph.preheader_0)| main@_bb_0)
                (=> main@.lr.ph.preheader_0
                    (or (and main@._crit_edge_0
                             |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                        (and main@_bb_0
                             |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    main@%_20_0)
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_0 1))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (not main@%_25_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_1 main@%_24_0))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_1))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
                main@.lr.ph_0
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_0 0))
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_1 main@%y.0.i1_0)))))
  (=> a!1 (main@.lr.ph @__VERIFIER_nondet_int_0 main@%y.0.i1_1 main@%x.0.i12_2))))
(rule (let ((a!1 (and (main@.lr.ph6.split
                  @__VERIFIER_nondet_int_0
                  main@%_1_0
                  main@%a.0.i3_0
                  main@%b.0.i2_0
                  main@%s.0.i4_0
                  main@%t.0.i5_0)
                true
                (= main@%_13_0 (+ main@%a.0.i3_0 1))
                (= main@%_14_0 (+ main@%b.0.i2_0 1))
                (= main@%_15_0 (+ main@%s.0.i4_0 main@%_13_0))
                (= main@%_16_0 (+ main@%t.0.i5_0 main@%_14_0))
                (= main@%..i_0 (+ main@%_16_0 main@%_13_0))
                (= main@%_17_0 @__VERIFIER_nondet_int_0)
                (= main@%_19_0 (= main@%_18_0 0))
                (=> main@._crit_edge.loopexit19_0
                    (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    main@%_19_0)
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%..i.lcssa_0 main@%..i_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%.lcssa23_0 main@%_15_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%..i.lcssa_1 main@%..i.lcssa_0))
                (=> (and main@._crit_edge.loopexit19_0 main@.lr.ph6.split_0)
                    (= main@%.lcssa23_1 main@%.lcssa23_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit19_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%t.0.i.lcssa_0 main@%..i.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%s.0.i.lcssa_0 main@%.lcssa23_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit19_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_bb_0))
                (=> (and main@verifier.error_0 main@_bb_0) main@%_25_0)
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_0 true))
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0 (not main@%y.0.i.lcssa_1))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph6.split.us
           @__VERIFIER_nondet_int_0
           main@%_1_0
           main@%a.0.i3.us_0
           main@%b.0.i2.us_0
           main@%s.0.i4.us_0
           main@%t.0.i5.us_0)
         true
         (= main@%_6_0 (+ main@%a.0.i3.us_0 1))
         (= main@%_7_0 (+ main@%b.0.i2.us_0 1))
         (= main@%_8_0 (+ main@%s.0.i4.us_0 main@%_6_0))
         (= main@%_9_0 (+ main@%t.0.i5.us_0 main@%_7_0))
         (= main@%_10_0 @__VERIFIER_nondet_int_0)
         (= main@%_12_0 (= main@%_11_0 0))
         (=> main@.lr.ph6.split.us_1
             (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0))
         main@.lr.ph6.split.us_1
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (not main@%_12_0))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%t.0.i5.us_1 main@%_9_0))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%s.0.i4.us_1 main@%_8_0))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%a.0.i3.us_1 main@%_6_0))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%b.0.i2.us_1 main@%_7_0))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%t.0.i5.us_2 main@%t.0.i5.us_1))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%s.0.i4.us_2 main@%s.0.i4.us_1))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%a.0.i3.us_2 main@%a.0.i3.us_1))
         (=> (and main@.lr.ph6.split.us_1 main@.lr.ph6.split.us_0)
             (= main@%b.0.i2.us_2 main@%b.0.i2.us_1)))
    (main@.lr.ph6.split.us
      @__VERIFIER_nondet_int_0
      main@%_1_0
      main@%a.0.i3.us_2
      main@%b.0.i2.us_2
      main@%s.0.i4.us_2
      main@%t.0.i5.us_2)))
(rule (let ((a!1 (and (main@.lr.ph6.split.us
                  @__VERIFIER_nondet_int_0
                  main@%_1_0
                  main@%a.0.i3.us_0
                  main@%b.0.i2.us_0
                  main@%s.0.i4.us_0
                  main@%t.0.i5.us_0)
                true
                (= main@%_6_0 (+ main@%a.0.i3.us_0 1))
                (= main@%_7_0 (+ main@%b.0.i2.us_0 1))
                (= main@%_8_0 (+ main@%s.0.i4.us_0 main@%_6_0))
                (= main@%_9_0 (+ main@%t.0.i5.us_0 main@%_7_0))
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    main@%_12_0)
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa22_0 main@%_9_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa_0 main@%_8_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa22_1 main@%.lcssa22_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%t.0.i.lcssa_0 main@%.lcssa22_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%s.0.i.lcssa_0 main@%.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|
                    main@._crit_edge_0)
                (=> |tuple(main@_bb_0, main@.lr.ph.preheader_0)| main@_bb_0)
                (=> main@.lr.ph.preheader_0
                    (or (and main@._crit_edge_0
                             |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                        (and main@_bb_0
                             |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    main@%_20_0)
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_0 1))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (not main@%_25_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_1 main@%_24_0))
                (=> (and main@._crit_edge_0
                         |tuple(main@._crit_edge_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_0))
                (=> (and main@_bb_0
                         |tuple(main@_bb_0, main@.lr.ph.preheader_0)|)
                    (= main@%x.0.i12_2 main@%x.0.i12_1))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
                main@.lr.ph_0
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_0 0))
                (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
                    (= main@%y.0.i1_1 main@%y.0.i1_0)))))
  (=> a!1 (main@.lr.ph @__VERIFIER_nondet_int_0 main@%y.0.i1_1 main@%x.0.i12_2))))
(rule (let ((a!1 (and (main@.lr.ph6.split.us
                  @__VERIFIER_nondet_int_0
                  main@%_1_0
                  main@%a.0.i3.us_0
                  main@%b.0.i2.us_0
                  main@%s.0.i4.us_0
                  main@%t.0.i5.us_0)
                true
                (= main@%_6_0 (+ main@%a.0.i3.us_0 1))
                (= main@%_7_0 (+ main@%b.0.i2.us_0 1))
                (= main@%_8_0 (+ main@%s.0.i4.us_0 main@%_6_0))
                (= main@%_9_0 (+ main@%t.0.i5.us_0 main@%_7_0))
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    main@%_12_0)
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa22_0 main@%_9_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa_0 main@%_8_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa22_1 main@%.lcssa22_0))
                (=> (and main@._crit_edge.loopexit_0 main@.lr.ph6.split.us_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%t.0.i.lcssa_0 main@%.lcssa22_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%s.0.i.lcssa_0 main@%.lcssa_1))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%t.0.i.lcssa_1 main@%t.0.i.lcssa_0))
                (=> (and main@._crit_edge_0 main@._crit_edge.loopexit_0)
                    (= main@%s.0.i.lcssa_1 main@%s.0.i.lcssa_0))
                (=> main@._crit_edge_0 (= main@%_20_0 (= main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                (=> (and main@_bb_0 main@._crit_edge_0) (not main@%_20_0))
                (=> main@_bb_0 (= main@%_22_0 (* main@%s.0.i.lcssa_1 (- 2))))
                (=> main@_bb_0 (= main@%_23_0 (+ main@%_22_0 2)))
                (=> main@_bb_0
                    (= main@%_24_0 (+ main@%_23_0 main@%t.0.i.lcssa_1)))
                (=> main@_bb_0 (= main@%_25_0 (< main@%_24_0 0)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@_bb_0))
                (=> (and main@verifier.error_0 main@_bb_0) main@%_25_0)
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_0 true))
                (=> (and main@verifier.error_0 main@_bb_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0 (not main@%y.0.i.lcssa_1))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@.lr.ph @__VERIFIER_nondet_int_0 main@%y.0.i1_0 main@%x.0.i12_0)
         true
         (= main@%_26_0 @__VERIFIER_nondet_int_0)
         (= main@%_28_0 (= main@%_27_0 0))
         (= main@%y.1.v.i_0 (ite main@%_28_0 2 1))
         (= main@%y.1.i_0 (+ main@%y.1.v.i_0 main@%y.0.i1_0))
         (= main@%_29_0 (> main@%y.1.i_0 main@%x.0.i12_0))
         (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.lr.ph_0))
         main@.lr.ph_1
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (not main@%_29_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0) (= main@%y.0.i1_1 main@%y.1.i_0))
         (=> (and main@.lr.ph_1 main@.lr.ph_0)
             (= main@%y.0.i1_2 main@%y.0.i1_1)))
    (main@.lr.ph @__VERIFIER_nondet_int_0 main@%y.0.i1_2 main@%x.0.i12_0)))
(rule (let ((a!1 (and (main@.lr.ph @__VERIFIER_nondet_int_0
                             main@%y.0.i1_0
                             main@%x.0.i12_0)
                true
                (= main@%_26_0 @__VERIFIER_nondet_int_0)
                (= main@%_28_0 (= main@%_27_0 0))
                (= main@%y.1.v.i_0 (ite main@%_28_0 2 1))
                (= main@%y.1.i_0 (+ main@%y.1.v.i_0 main@%y.0.i1_0))
                (= main@%_29_0 (> main@%y.1.i_0 main@%x.0.i12_0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@.lr.ph_0))
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    main@%_29_0)
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    (= main@%y.1.i.lcssa_0 main@%y.1.i_0))
                (=> (and main@verifier.error.loopexit_0 main@.lr.ph_0)
                    (= main@%y.1.i.lcssa_1 main@%y.1.i.lcssa_0))
                (=> main@verifier.error.loopexit_0
                    (= main@%phitmp_0 (< main@%y.1.i.lcssa_1 5)))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_0 main@%phitmp_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0 (not main@%y.0.i.lcssa_1))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

