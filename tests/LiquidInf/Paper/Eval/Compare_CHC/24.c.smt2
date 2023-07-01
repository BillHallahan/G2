(set-info :original "/tmp/sea-YgztxI/24.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@_bb (Int Int Int Int ))
(declare-rel main@.preheader (Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_12_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%k.0.i1_2 Int )
(declare-var main@%_6_0 Bool )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%i.0.i_0 Int )
(declare-var main@%i.0.i_1 Int )
(declare-var main@._crit_edge3_0 Bool )
(declare-var main@%_13_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@%i.0.i_2 Int )
(declare-var main@.preheader.preheader_0 Bool )
(declare-var main@.preheader_0 Bool )
(declare-var main@%j.0.i2_0 Int )
(declare-var main@%j.0.i2_1 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@._crit_edge3.loopexit_0 Bool )
(declare-var main@.preheader_1 Bool )
(declare-var main@%j.0.i2_2 Int )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%k.0.i1_0 Int )
(declare-var main@%k.0.i1_1 Int )
(declare-var main@%_10_0 Int )
(declare-var main@_bb1_0 Bool )
(declare-var main@._crit_edge.loopexit_0 Bool )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (=> main@_bb_0 (and main@_bb_0 main@entry_0))
         main@_bb_0
         (=> (and main@_bb_0 main@entry_0) (= main@%i.0.i_0 0))
         (=> (and main@_bb_0 main@entry_0) (= main@%i.0.i_1 main@%i.0.i_0)))
    (main@_bb main@%i.0.i_1 main@%_1_0 main@%_0_0 main@%_2_0)))
(rule (let ((a!1 (and (main@_bb main@%i.0.i_0 main@%_1_0 main@%_0_0 main@%_2_0)
                true
                (= main@%_4_0 (< main@%i.0.i_0 main@%_2_0))
                main@%_4_0
                (= main@%_5_0 (< main@%i.0.i_0 main@%_1_0))
                (=> main@._crit_edge3_0 (and main@._crit_edge3_0 main@_bb_0))
                (=> (and main@._crit_edge3_0 main@_bb_0) (not main@%_5_0))
                (=> main@._crit_edge3_0 (= main@%_13_0 (+ main@%i.0.i_0 1)))
                (=> main@_bb_1 (and main@_bb_1 main@._crit_edge3_0))
                main@_bb_1
                (=> (and main@_bb_1 main@._crit_edge3_0)
                    (= main@%i.0.i_1 main@%_13_0))
                (=> (and main@_bb_1 main@._crit_edge3_0)
                    (= main@%i.0.i_2 main@%i.0.i_1)))))
  (=> a!1 (main@_bb main@%i.0.i_2 main@%_1_0 main@%_0_0 main@%_2_0))))
(rule (=> (and (main@_bb main@%i.0.i_0 main@%_1_0 main@%_0_0 main@%_2_0)
         true
         (= main@%_4_0 (< main@%i.0.i_0 main@%_2_0))
         main@%_4_0
         (= main@%_5_0 (< main@%i.0.i_0 main@%_1_0))
         (=> main@.preheader.preheader_0
             (and main@.preheader.preheader_0 main@_bb_0))
         (=> (and main@.preheader.preheader_0 main@_bb_0) main@%_5_0)
         (=> main@.preheader_0
             (and main@.preheader_0 main@.preheader.preheader_0))
         main@.preheader_0
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%j.0.i2_0 main@%i.0.i_0))
         (=> (and main@.preheader_0 main@.preheader.preheader_0)
             (= main@%j.0.i2_1 main@%j.0.i2_0)))
    (main@.preheader main@%i.0.i_0
                     main@%j.0.i2_1
                     main@%_1_0
                     main@%_0_0
                     main@%_2_0)))
(rule (let ((a!1 (and (main@.preheader main@%i.0.i_0
                                 main@%j.0.i2_0
                                 main@%_1_0
                                 main@%_0_0
                                 main@%_2_0)
                true
                (= main@%_6_0 (< main@%j.0.i2_0 main@%_0_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) (not main@%_6_0))
                (=> main@._crit_edge_0 (= main@%_11_0 (+ main@%j.0.i2_0 1)))
                (=> main@._crit_edge_0
                    (= main@%_12_0 (< main@%_11_0 main@%_1_0)))
                (=> main@._crit_edge3.loopexit_0
                    (and main@._crit_edge3.loopexit_0 main@._crit_edge_0))
                (=> (and main@._crit_edge3.loopexit_0 main@._crit_edge_0)
                    (not main@%_12_0))
                (=> main@._crit_edge3_0
                    (and main@._crit_edge3_0 main@._crit_edge3.loopexit_0))
                (=> main@._crit_edge3_0 (= main@%_13_0 (+ main@%i.0.i_0 1)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge3_0))
                main@_bb_0
                (=> (and main@_bb_0 main@._crit_edge3_0)
                    (= main@%i.0.i_1 main@%_13_0))
                (=> (and main@_bb_0 main@._crit_edge3_0)
                    (= main@%i.0.i_2 main@%i.0.i_1)))))
  (=> a!1 (main@_bb main@%i.0.i_2 main@%_1_0 main@%_0_0 main@%_2_0))))
(rule (let ((a!1 (and (main@.preheader main@%i.0.i_0
                                 main@%j.0.i2_0
                                 main@%_1_0
                                 main@%_0_0
                                 main@%_2_0)
                true
                (= main@%_6_0 (< main@%j.0.i2_0 main@%_0_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@.preheader_0))
                (=> (and main@._crit_edge_0 main@.preheader_0) (not main@%_6_0))
                (=> main@._crit_edge_0 (= main@%_11_0 (+ main@%j.0.i2_0 1)))
                (=> main@._crit_edge_0
                    (= main@%_12_0 (< main@%_11_0 main@%_1_0)))
                (=> main@.preheader_1
                    (and main@.preheader_1 main@._crit_edge_0))
                main@.preheader_1
                (=> (and main@.preheader_1 main@._crit_edge_0) main@%_12_0)
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%j.0.i2_1 main@%_11_0))
                (=> (and main@.preheader_1 main@._crit_edge_0)
                    (= main@%j.0.i2_2 main@%j.0.i2_1)))))
  (=> a!1
      (main@.preheader main@%i.0.i_0
                       main@%j.0.i2_2
                       main@%_1_0
                       main@%_0_0
                       main@%_2_0))))
(rule (=> (and (main@.preheader main@%i.0.i_0
                          main@%j.0.i2_0
                          main@%_1_0
                          main@%_0_0
                          main@%_2_0)
         true
         (= main@%_6_0 (< main@%j.0.i2_0 main@%_0_0))
         (=> main@.lr.ph.preheader_0
             (and main@.lr.ph.preheader_0 main@.preheader_0))
         (=> (and main@.lr.ph.preheader_0 main@.preheader_0) main@%_6_0)
         (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
         main@.lr.ph_0
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%k.0.i1_0 main@%j.0.i2_0))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%k.0.i1_1 main@%k.0.i1_0)))
    (main@.lr.ph main@%i.0.i_0
                 main@%j.0.i2_0
                 main@%_1_0
                 main@%_0_0
                 main@%k.0.i1_1
                 main@%_2_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%j.0.i2_0
                             main@%_1_0
                             main@%_0_0
                             main@%k.0.i1_0
                             main@%_2_0)
                true
                (= main@%_9_0 (< main@%k.0.i1_0 main@%i.0.i_0))
                (= main@%_10_0 (+ main@%k.0.i1_0 1))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_9_0))
                (=> main@_bb1_0 (= main@%_8_0 (< main@%_10_0 main@%_0_0)))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb1_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb1_0)
                    (not main@%_8_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> main@._crit_edge_0 (= main@%_11_0 (+ main@%j.0.i2_0 1)))
                (=> main@._crit_edge_0
                    (= main@%_12_0 (< main@%_11_0 main@%_1_0)))
                (=> main@._crit_edge3.loopexit_0
                    (and main@._crit_edge3.loopexit_0 main@._crit_edge_0))
                (=> (and main@._crit_edge3.loopexit_0 main@._crit_edge_0)
                    (not main@%_12_0))
                (=> main@._crit_edge3_0
                    (and main@._crit_edge3_0 main@._crit_edge3.loopexit_0))
                (=> main@._crit_edge3_0 (= main@%_13_0 (+ main@%i.0.i_0 1)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge3_0))
                main@_bb_0
                (=> (and main@_bb_0 main@._crit_edge3_0)
                    (= main@%i.0.i_1 main@%_13_0))
                (=> (and main@_bb_0 main@._crit_edge3_0)
                    (= main@%i.0.i_2 main@%i.0.i_1)))))
  (=> a!1 (main@_bb main@%i.0.i_2 main@%_1_0 main@%_0_0 main@%_2_0))))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%j.0.i2_0
                             main@%_1_0
                             main@%_0_0
                             main@%k.0.i1_0
                             main@%_2_0)
                true
                (= main@%_9_0 (< main@%k.0.i1_0 main@%i.0.i_0))
                (= main@%_10_0 (+ main@%k.0.i1_0 1))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_9_0))
                (=> main@_bb1_0 (= main@%_8_0 (< main@%_10_0 main@%_0_0)))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@_bb1_0))
                (=> (and main@._crit_edge.loopexit_0 main@_bb1_0)
                    (not main@%_8_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> main@._crit_edge_0 (= main@%_11_0 (+ main@%j.0.i2_0 1)))
                (=> main@._crit_edge_0
                    (= main@%_12_0 (< main@%_11_0 main@%_1_0)))
                (=> main@.preheader_0
                    (and main@.preheader_0 main@._crit_edge_0))
                main@.preheader_0
                (=> (and main@.preheader_0 main@._crit_edge_0) main@%_12_0)
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%j.0.i2_1 main@%_11_0))
                (=> (and main@.preheader_0 main@._crit_edge_0)
                    (= main@%j.0.i2_2 main@%j.0.i2_1)))))
  (=> a!1
      (main@.preheader main@%i.0.i_0
                       main@%j.0.i2_2
                       main@%_1_0
                       main@%_0_0
                       main@%_2_0))))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%j.0.i2_0
                             main@%_1_0
                             main@%_0_0
                             main@%k.0.i1_0
                             main@%_2_0)
                true
                (= main@%_9_0 (< main@%k.0.i1_0 main@%i.0.i_0))
                (= main@%_10_0 (+ main@%k.0.i1_0 1))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_9_0))
                (=> main@_bb1_0 (= main@%_8_0 (< main@%_10_0 main@%_0_0)))
                (=> main@.lr.ph_1 (and main@.lr.ph_1 main@_bb1_0))
                main@.lr.ph_1
                (=> (and main@.lr.ph_1 main@_bb1_0) main@%_8_0)
                (=> (and main@.lr.ph_1 main@_bb1_0)
                    (= main@%k.0.i1_1 main@%_10_0))
                (=> (and main@.lr.ph_1 main@_bb1_0)
                    (= main@%k.0.i1_2 main@%k.0.i1_1)))))
  (=> a!1
      (main@.lr.ph main@%i.0.i_0
                   main@%j.0.i2_0
                   main@%_1_0
                   main@%_0_0
                   main@%k.0.i1_2
                   main@%_2_0))))
(rule (=> (and (main@.lr.ph main@%i.0.i_0
                      main@%j.0.i2_0
                      main@%_1_0
                      main@%_0_0
                      main@%k.0.i1_0
                      main@%_2_0)
         true
         (= main@%_9_0 (< main@%k.0.i1_0 main@%i.0.i_0))
         (= main@%_10_0 (+ main@%k.0.i1_0 1))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@.lr.ph_0))
         (=> (and main@verifier.error_0 main@.lr.ph_0) main@%_9_0)
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(query main@verifier.error.split)

