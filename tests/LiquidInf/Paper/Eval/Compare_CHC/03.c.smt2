(set-info :original "/tmp/sea-fggUix/03.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry ())
(declare-rel main@entry.split (Int Int ))
(declare-rel main@entry.split.us (Int Int Int ))
(declare-rel main@.lr.ph.us (Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_5_0 Bool )
(declare-var main@%_6_0 Bool )
(declare-var main@%_3_0 Bool )
(declare-var main@%i.1.i1.us_2 Int )
(declare-var main@%_9_0 Bool )
(declare-var main@%k.0.i_2 Int )
(declare-var main@%_2_0 Bool )
(declare-var main@entry_0 Bool )
(declare-var main@%_0_0 Int )
(declare-var main@%_1_0 Int )
(declare-var main@entry.split.preheader_0 Bool )
(declare-var main@entry.split_0 Bool )
(declare-var main@%k.0.i_0 Int )
(declare-var main@%k.0.i_1 Int )
(declare-var main@entry.split.us.preheader_0 Bool )
(declare-var main@entry.split.us_0 Bool )
(declare-var main@%k.0.i.us_0 Int )
(declare-var main@%k.0.i.us_1 Int )
(declare-var main@%_10_0 Int )
(declare-var main@entry.split_1 Bool )
(declare-var main@.lr.ph.us_0 Bool )
(declare-var main@%i.1.i1.us_0 Int )
(declare-var main@%i.1.i1.us_1 Int )
(declare-var main@%_7_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@._crit_edge.us_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@%k.0.i.us_2 Int )
(declare-var main@.lr.ph.us_1 Bool )
(declare-var main@verifier.error_0 Bool )
(declare-var main@verifier.error.split_0 Bool )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule main@entry)
(rule (=> (and main@entry
         true
         (= main@%_2_0 (> main@%_0_0 1))
         (=> main@entry.split.preheader_0
             (and main@entry.split.preheader_0 main@entry_0))
         (=> (and main@entry.split.preheader_0 main@entry_0) (not main@%_2_0))
         (=> main@entry.split_0
             (and main@entry.split_0 main@entry.split.preheader_0))
         main@entry.split_0
         (=> (and main@entry.split_0 main@entry.split.preheader_0)
             (= main@%k.0.i_0 1))
         (=> (and main@entry.split_0 main@entry.split.preheader_0)
             (= main@%k.0.i_1 main@%k.0.i_0)))
    (main@entry.split main@%_1_0 main@%k.0.i_1)))
(rule (=> (and main@entry
         true
         (= main@%_2_0 (> main@%_0_0 1))
         (=> main@entry.split.us.preheader_0
             (and main@entry.split.us.preheader_0 main@entry_0))
         (=> (and main@entry.split.us.preheader_0 main@entry_0) main@%_2_0)
         (=> main@entry.split.us_0
             (and main@entry.split.us_0 main@entry.split.us.preheader_0))
         main@entry.split.us_0
         (=> (and main@entry.split.us_0 main@entry.split.us.preheader_0)
             (= main@%k.0.i.us_0 1))
         (=> (and main@entry.split.us_0 main@entry.split.us.preheader_0)
             (= main@%k.0.i.us_1 main@%k.0.i.us_0)))
    (main@entry.split.us main@%k.0.i.us_1 main@%_0_0 main@%_1_0)))
(rule (=> (and (main@entry.split main@%_1_0 main@%k.0.i_0)
         true
         (= main@%_9_0 (< main@%k.0.i_0 main@%_1_0))
         main@%_9_0
         (= main@%_10_0 (+ main@%k.0.i_0 1))
         (=> main@entry.split_1 (and main@entry.split_1 main@entry.split_0))
         main@entry.split_1
         (=> (and main@entry.split_1 main@entry.split_0)
             (= main@%k.0.i_1 main@%_10_0))
         (=> (and main@entry.split_1 main@entry.split_0)
             (= main@%k.0.i_2 main@%k.0.i_1)))
    (main@entry.split main@%_1_0 main@%k.0.i_2)))
(rule (=> (and (main@entry.split.us main@%k.0.i.us_0 main@%_0_0 main@%_1_0)
         true
         (= main@%_3_0 (< main@%k.0.i.us_0 main@%_1_0))
         main@%_3_0
         (=> main@.lr.ph.us_0 (and main@.lr.ph.us_0 main@entry.split.us_0))
         main@.lr.ph.us_0
         (=> (and main@.lr.ph.us_0 main@entry.split.us_0)
             (= main@%i.1.i1.us_0 1))
         (=> (and main@.lr.ph.us_0 main@entry.split.us_0)
             (= main@%i.1.i1.us_1 main@%i.1.i1.us_0)))
    (main@.lr.ph.us main@%k.0.i.us_0 main@%_0_0 main@%i.1.i1.us_1 main@%_1_0)))
(rule (let ((a!1 (and (main@.lr.ph.us main@%k.0.i.us_0
                                main@%_0_0
                                main@%i.1.i1.us_0
                                main@%_1_0)
                true
                (= main@%_6_0 (> main@%i.1.i1.us_0 0))
                (= main@%_7_0 (+ main@%i.1.i1.us_0 1))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph.us_0))
                (=> (and main@_bb_0 main@.lr.ph.us_0) main@%_6_0)
                (=> main@_bb_0 (= main@%_5_0 (< main@%_7_0 main@%_0_0)))
                (=> main@._crit_edge.us_0
                    (and main@._crit_edge.us_0 main@_bb_0))
                (=> (and main@._crit_edge.us_0 main@_bb_0) (not main@%_5_0))
                (=> main@._crit_edge.us_0 (= main@%_8_0 (+ main@%k.0.i.us_0 1)))
                (=> main@entry.split.us_0
                    (and main@entry.split.us_0 main@._crit_edge.us_0))
                main@entry.split.us_0
                (=> (and main@entry.split.us_0 main@._crit_edge.us_0)
                    (= main@%k.0.i.us_1 main@%_8_0))
                (=> (and main@entry.split.us_0 main@._crit_edge.us_0)
                    (= main@%k.0.i.us_2 main@%k.0.i.us_1)))))
  (=> a!1 (main@entry.split.us main@%k.0.i.us_2 main@%_0_0 main@%_1_0))))
(rule (let ((a!1 (and (main@.lr.ph.us main@%k.0.i.us_0
                                main@%_0_0
                                main@%i.1.i1.us_0
                                main@%_1_0)
                true
                (= main@%_6_0 (> main@%i.1.i1.us_0 0))
                (= main@%_7_0 (+ main@%i.1.i1.us_0 1))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph.us_0))
                (=> (and main@_bb_0 main@.lr.ph.us_0) main@%_6_0)
                (=> main@_bb_0 (= main@%_5_0 (< main@%_7_0 main@%_0_0)))
                (=> main@.lr.ph.us_1 (and main@.lr.ph.us_1 main@_bb_0))
                main@.lr.ph.us_1
                (=> (and main@.lr.ph.us_1 main@_bb_0) main@%_5_0)
                (=> (and main@.lr.ph.us_1 main@_bb_0)
                    (= main@%i.1.i1.us_1 main@%_7_0))
                (=> (and main@.lr.ph.us_1 main@_bb_0)
                    (= main@%i.1.i1.us_2 main@%i.1.i1.us_1)))))
  (=> a!1
      (main@.lr.ph.us main@%k.0.i.us_0 main@%_0_0 main@%i.1.i1.us_2 main@%_1_0))))
(rule (=> (and (main@.lr.ph.us main@%k.0.i.us_0
                         main@%_0_0
                         main@%i.1.i1.us_0
                         main@%_1_0)
         true
         (= main@%_6_0 (> main@%i.1.i1.us_0 0))
         (= main@%_7_0 (+ main@%i.1.i1.us_0 1))
         (=> main@verifier.error_0 (and main@verifier.error_0 main@.lr.ph.us_0))
         (=> (and main@verifier.error_0 main@.lr.ph.us_0) (not main@%_6_0))
         (=> main@verifier.error.split_0
             (and main@verifier.error.split_0 main@verifier.error_0))
         main@verifier.error.split_0)
    main@verifier.error.split))
(query main@verifier.error.split)

