(set-info :original "/tmp/sea-UfTl04/43.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@_bb (Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_14_0 Bool )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%.y.0.i.lcssa_1 Int )
(declare-var main@%_8_0 Bool )
(declare-var main@%y.0.i1_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@%_7_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_9_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%y.0.i1_0 Int )
(declare-var main@%y.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%y.0.i.lcssa_0 Int )
(declare-var main@%y.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%.y.0.i_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%.y.0.i.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                (not main@%_4_0)
                (= main@%_5_0 @__VERIFIER_nondet_int_0)
                (= main@%_7_0 (= main@%_6_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) (not main@%_7_0))
                (=> main@.lr.ph_0 (= main@%_8_0 (> main@%_1_0 0)))
                (=> main@.lr.ph_0 (= main@%_9_0 (ite main@%_8_0 main@%_1_0 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.0.i1_0 main@%_3_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.0.i1_1 main@%y.0.i1_0)))))
  (=> a!1
      (main@_bb main@%_3_0 main@%y.0.i1_1 main@%_9_0 @__VERIFIER_nondet_int_0))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_1_0 main@%_3_0))
                (not main@%_4_0)
                (= main@%_5_0 @__VERIFIER_nondet_int_0)
                (= main@%_7_0 (= main@%_6_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_7_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%y.0.i.lcssa_0 main@%_3_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_14_0 (< main@%y.0.i.lcssa_1 main@%_3_0)))
                (=> main@verifier.error_0 main@%_14_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@_bb main@%_3_0
                   main@%y.0.i1_0
                   main@%_9_0
                   @__VERIFIER_nondet_int_0)
         true
         (= main@%.y.0.i_0 (+ main@%y.0.i1_0 main@%_9_0))
         (= main@%_11_0 @__VERIFIER_nondet_int_0)
         (= main@%_13_0 (= main@%_12_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_13_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.0.i1_1 main@%.y.0.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.0.i1_2 main@%y.0.i1_1)))
    (main@_bb main@%_3_0 main@%y.0.i1_2 main@%_9_0 @__VERIFIER_nondet_int_0)))
(rule (let ((a!1 (and (main@_bb main@%_3_0
                          main@%y.0.i1_0
                          main@%_9_0
                          @__VERIFIER_nondet_int_0)
                true
                (= main@%.y.0.i_0 (+ main@%y.0.i1_0 main@%_9_0))
                (= main@%_11_0 @__VERIFIER_nondet_int_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@_bb_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0) main@%_13_0)
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.y.0.i.lcssa_0 main@%.y.0.i_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.y.0.i.lcssa_1 main@%.y.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_0 main@%.y.0.i.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%y.0.i.lcssa_1 main@%y.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_14_0 (< main@%y.0.i.lcssa_1 main@%_3_0)))
                (=> main@verifier.error_0 main@%_14_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

