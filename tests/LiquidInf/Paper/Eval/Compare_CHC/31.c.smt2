(set-info :original "/tmp/sea-vNdb0n/31.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@_bb (Int Int Int Int Int ))
(declare-rel main@.lr.ph (Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_21_0 Bool )
(declare-var main@%_17_0 Int )
(declare-var main@%_18_0 Bool )
(declare-var main@%_14_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Bool )
(declare-var main@%_8_0 Bool )
(declare-var main@%_9_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Int )
(declare-var main@%_5_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%i.0.i_0 Int )
(declare-var main@%i.0.i_1 Int )
(declare-var main@._crit_edge_0 Bool )
(declare-var main@%_22_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@%i.0.i_2 Int )
(declare-var main@.lr.ph.preheader_0 Bool )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%j.0.i1_0 Int )
(declare-var main@%j.0.i1_1 Int )
(declare-var main@_bb1_0 Bool )
(declare-var main@.backedge.loopexit_0 Bool )
(declare-var main@%_15_0 Int )
(declare-var main@_bb2_0 Bool )
(declare-var main@_bb3_0 Bool )
(declare-var main@%_20_0 Int )
(declare-var main@.backedge_0 Bool )
(declare-var main@%j.0.i.be_0 Int )
(declare-var main@%j.0.i.be_1 Int )
(declare-var main@%j.0.i.be_2 Int )
(declare-var main@._crit_edge.loopexit_0 Bool )
(declare-var main@.lr.ph_1 Bool )
(declare-var main@%j.0.i1_2 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var |tuple(main@_bb2_0, main@verifier.error_0)| Bool )
(declare-var |tuple(main@_bb1_0, main@verifier.error_0)| Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (=> (and (main@entry @__VERIFIER_nondet_int_0)
         true
         (= main@%_0_0 @__VERIFIER_nondet_int_0)
         (= main@%_2_0 @__VERIFIER_nondet_int_0)
         (= main@%_4_0 (+ main@%_1_0 1))
         (= main@%_5_0 (< main@%_4_0 main@%_3_0))
         main@%_5_0
         (= main@%_6_0 (+ main@%_3_0 5))
         (=> main@_bb_0 (and main@_bb_0 main@entry_0))
         main@_bb_0
         (=> (and main@_bb_0 main@entry_0) (= main@%i.0.i_0 0))
         (=> (and main@_bb_0 main@entry_0) (= main@%i.0.i_1 main@%i.0.i_0)))
    (main@_bb main@%i.0.i_1
              main@%_1_0
              main@%_6_0
              @__VERIFIER_nondet_int_0
              main@%_3_0)))
(rule (let ((a!1 (and (main@_bb main@%i.0.i_0
                          main@%_1_0
                          main@%_6_0
                          @__VERIFIER_nondet_int_0
                          main@%_3_0)
                true
                (= main@%_8_0 (< main@%i.0.i_0 main@%_3_0))
                main@%_8_0
                (= main@%_9_0 (< main@%i.0.i_0 main@%_1_0))
                (=> main@._crit_edge_0 (and main@._crit_edge_0 main@_bb_0))
                (=> (and main@._crit_edge_0 main@_bb_0) (not main@%_9_0))
                (=> main@._crit_edge_0 (= main@%_22_0 (+ main@%i.0.i_0 4)))
                (=> main@_bb_1 (and main@_bb_1 main@._crit_edge_0))
                main@_bb_1
                (=> (and main@_bb_1 main@._crit_edge_0)
                    (= main@%i.0.i_1 main@%_22_0))
                (=> (and main@_bb_1 main@._crit_edge_0)
                    (= main@%i.0.i_2 main@%i.0.i_1)))))
  (=> a!1
      (main@_bb main@%i.0.i_2
                main@%_1_0
                main@%_6_0
                @__VERIFIER_nondet_int_0
                main@%_3_0))))
(rule (=> (and (main@_bb main@%i.0.i_0
                   main@%_1_0
                   main@%_6_0
                   @__VERIFIER_nondet_int_0
                   main@%_3_0)
         true
         (= main@%_8_0 (< main@%i.0.i_0 main@%_3_0))
         main@%_8_0
         (= main@%_9_0 (< main@%i.0.i_0 main@%_1_0))
         (=> main@.lr.ph.preheader_0 (and main@.lr.ph.preheader_0 main@_bb_0))
         (=> (and main@.lr.ph.preheader_0 main@_bb_0) main@%_9_0)
         (=> main@.lr.ph_0 (and main@.lr.ph_0 main@.lr.ph.preheader_0))
         main@.lr.ph_0
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%j.0.i1_0 main@%i.0.i_0))
         (=> (and main@.lr.ph_0 main@.lr.ph.preheader_0)
             (= main@%j.0.i1_1 main@%j.0.i1_0)))
    (main@.lr.ph main@%i.0.i_0
                 main@%_1_0
                 main@%j.0.i1_1
                 main@%_6_0
                 @__VERIFIER_nondet_int_0
                 main@%_3_0)))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%_1_0
                             main@%j.0.i1_0
                             main@%_6_0
                             @__VERIFIER_nondet_int_0
                             main@%_3_0)
                true
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_12_0))
                (=> main@_bb1_0 (= main@%_14_0 (> main@%j.0.i1_0 (- 1))))
                (=> main@.backedge.loopexit_0
                    (and main@.backedge.loopexit_0 main@_bb1_0))
                (=> (and main@.backedge.loopexit_0 main@_bb1_0) main@%_14_0)
                (=> main@.backedge.loopexit_0
                    (= main@%_15_0 (+ main@%j.0.i1_0 1)))
                (=> main@_bb2_0 (and main@_bb2_0 main@.lr.ph_0))
                (=> (and main@_bb2_0 main@.lr.ph_0) main@%_12_0)
                (=> main@_bb2_0 (= main@%_17_0 (+ main@%_6_0 main@%j.0.i1_0)))
                (=> main@_bb2_0 (= main@%_18_0 (> main@%_17_0 main@%i.0.i_0)))
                (=> main@_bb3_0 (and main@_bb3_0 main@_bb2_0))
                (=> (and main@_bb3_0 main@_bb2_0) main@%_18_0)
                (=> main@_bb3_0 (= main@%_20_0 (+ main@%j.0.i1_0 2)))
                (=> main@.backedge_0
                    (or (and main@.backedge_0 main@.backedge.loopexit_0)
                        (and main@.backedge_0 main@_bb3_0)))
                (=> (and main@.backedge_0 main@.backedge.loopexit_0)
                    (= main@%j.0.i.be_0 main@%_15_0))
                (=> (and main@.backedge_0 main@_bb3_0)
                    (= main@%j.0.i.be_1 main@%_20_0))
                (=> (and main@.backedge_0 main@.backedge.loopexit_0)
                    (= main@%j.0.i.be_2 main@%j.0.i.be_0))
                (=> (and main@.backedge_0 main@_bb3_0)
                    (= main@%j.0.i.be_2 main@%j.0.i.be_1))
                (=> main@.backedge_0
                    (= main@%_21_0 (< main@%j.0.i.be_2 main@%_1_0)))
                (=> main@._crit_edge.loopexit_0
                    (and main@._crit_edge.loopexit_0 main@.backedge_0))
                (=> (and main@._crit_edge.loopexit_0 main@.backedge_0)
                    (not main@%_21_0))
                (=> main@._crit_edge_0
                    (and main@._crit_edge_0 main@._crit_edge.loopexit_0))
                (=> main@._crit_edge_0 (= main@%_22_0 (+ main@%i.0.i_0 4)))
                (=> main@_bb_0 (and main@_bb_0 main@._crit_edge_0))
                main@_bb_0
                (=> (and main@_bb_0 main@._crit_edge_0)
                    (= main@%i.0.i_1 main@%_22_0))
                (=> (and main@_bb_0 main@._crit_edge_0)
                    (= main@%i.0.i_2 main@%i.0.i_1)))))
  (=> a!1
      (main@_bb main@%i.0.i_2
                main@%_1_0
                main@%_6_0
                @__VERIFIER_nondet_int_0
                main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%_1_0
                             main@%j.0.i1_0
                             main@%_6_0
                             @__VERIFIER_nondet_int_0
                             main@%_3_0)
                true
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_12_0))
                (=> main@_bb1_0 (= main@%_14_0 (> main@%j.0.i1_0 (- 1))))
                (=> main@.backedge.loopexit_0
                    (and main@.backedge.loopexit_0 main@_bb1_0))
                (=> (and main@.backedge.loopexit_0 main@_bb1_0) main@%_14_0)
                (=> main@.backedge.loopexit_0
                    (= main@%_15_0 (+ main@%j.0.i1_0 1)))
                (=> main@_bb2_0 (and main@_bb2_0 main@.lr.ph_0))
                (=> (and main@_bb2_0 main@.lr.ph_0) main@%_12_0)
                (=> main@_bb2_0 (= main@%_17_0 (+ main@%_6_0 main@%j.0.i1_0)))
                (=> main@_bb2_0 (= main@%_18_0 (> main@%_17_0 main@%i.0.i_0)))
                (=> main@_bb3_0 (and main@_bb3_0 main@_bb2_0))
                (=> (and main@_bb3_0 main@_bb2_0) main@%_18_0)
                (=> main@_bb3_0 (= main@%_20_0 (+ main@%j.0.i1_0 2)))
                (=> main@.backedge_0
                    (or (and main@.backedge_0 main@.backedge.loopexit_0)
                        (and main@.backedge_0 main@_bb3_0)))
                (=> (and main@.backedge_0 main@.backedge.loopexit_0)
                    (= main@%j.0.i.be_0 main@%_15_0))
                (=> (and main@.backedge_0 main@_bb3_0)
                    (= main@%j.0.i.be_1 main@%_20_0))
                (=> (and main@.backedge_0 main@.backedge.loopexit_0)
                    (= main@%j.0.i.be_2 main@%j.0.i.be_0))
                (=> (and main@.backedge_0 main@_bb3_0)
                    (= main@%j.0.i.be_2 main@%j.0.i.be_1))
                (=> main@.backedge_0
                    (= main@%_21_0 (< main@%j.0.i.be_2 main@%_1_0)))
                (=> main@.lr.ph_1 (and main@.lr.ph_1 main@.backedge_0))
                main@.lr.ph_1
                (=> (and main@.lr.ph_1 main@.backedge_0) main@%_21_0)
                (=> (and main@.lr.ph_1 main@.backedge_0)
                    (= main@%j.0.i1_1 main@%j.0.i.be_2))
                (=> (and main@.lr.ph_1 main@.backedge_0)
                    (= main@%j.0.i1_2 main@%j.0.i1_1)))))
  (=> a!1
      (main@.lr.ph main@%i.0.i_0
                   main@%_1_0
                   main@%j.0.i1_2
                   main@%_6_0
                   @__VERIFIER_nondet_int_0
                   main@%_3_0))))
(rule (let ((a!1 (and (main@.lr.ph main@%i.0.i_0
                             main@%_1_0
                             main@%j.0.i1_0
                             main@%_6_0
                             @__VERIFIER_nondet_int_0
                             main@%_3_0)
                true
                (= main@%_10_0 @__VERIFIER_nondet_int_0)
                (= main@%_12_0 (= main@%_11_0 0))
                (=> main@_bb1_0 (and main@_bb1_0 main@.lr.ph_0))
                (=> (and main@_bb1_0 main@.lr.ph_0) (not main@%_12_0))
                (=> main@_bb1_0 (= main@%_14_0 (> main@%j.0.i1_0 (- 1))))
                (=> main@_bb2_0 (and main@_bb2_0 main@.lr.ph_0))
                (=> (and main@_bb2_0 main@.lr.ph_0) main@%_12_0)
                (=> main@_bb2_0 (= main@%_17_0 (+ main@%_6_0 main@%j.0.i1_0)))
                (=> main@_bb2_0 (= main@%_18_0 (> main@%_17_0 main@%i.0.i_0)))
                (=> |tuple(main@_bb2_0, main@verifier.error_0)| main@_bb2_0)
                (=> |tuple(main@_bb1_0, main@verifier.error_0)| main@_bb1_0)
                (=> main@verifier.error_0
                    (or (and main@_bb2_0
                             |tuple(main@_bb2_0, main@verifier.error_0)|)
                        (and main@_bb1_0
                             |tuple(main@_bb1_0, main@verifier.error_0)|)))
                (=> (and main@_bb2_0
                         |tuple(main@_bb2_0, main@verifier.error_0)|)
                    (not main@%_18_0))
                (=> (and main@_bb1_0
                         |tuple(main@_bb1_0, main@verifier.error_0)|)
                    (not main@%_14_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

