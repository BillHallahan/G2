(set-info :original "/tmp/sea-JqBzYK/13.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@_bb (Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_11_0 Bool )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Int )
(declare-var main@%_14_0 Bool )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%_10_0 Bool )
(declare-var main@%k.1.i.lcssa_1 Int )
(declare-var main@%j.1.i.lcssa_1 Int )
(declare-var main@%_5_0 Bool )
(declare-var main@%k.0.i2_2 Int )
(declare-var main@%j.0.i1_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%j.1.v.i_0 Int )
(declare-var main@%_6_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%k.0.i2_0 Int )
(declare-var main@%j.0.i1_0 Int )
(declare-var main@%k.0.i2_1 Int )
(declare-var main@%j.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%k.0.i.lcssa_0 Int )
(declare-var main@%j.0.i.lcssa_0 Int )
(declare-var main@%k.0.i.lcssa_1 Int )
(declare-var main@%j.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%j.1.i_0 Int )
(declare-var main@%k.1.i_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%k.1.i.lcssa_0 Int )
(declare-var main@%j.1.i.lcssa_0 Int )
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
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) (not main@%_4_0))
                (=> main@.lr.ph_0 (= main@%_5_0 (= main@%_1_0 0)))
                (=> main@.lr.ph_0 (= main@%j.1.v.i_0 (ite main@%_5_0 2 4)))
                (=> main@.lr.ph_0 (= main@%_6_0 (ite main@%_5_0 1 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%k.0.i2_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%j.0.i1_0 2))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%k.0.i2_1 main@%k.0.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%j.0.i1_1 main@%j.0.i1_0)))))
  (=> a!1
      (main@_bb main@%j.0.i1_1
                main@%j.1.v.i_0
                main@%k.0.i2_1
                main@%_6_0
                @__VERIFIER_nondet_int_0))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_4_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%k.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_0 2))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%k.0.i.lcssa_1 main@%k.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_11_0 (= main@%k.0.i.lcssa_1 0)))
                (=> main@verifier.error_0 (not main@%_11_0))
                (=> main@verifier.error_0
                    (= main@%_12_0 (* main@%k.0.i.lcssa_1 2)))
                (=> main@verifier.error_0 (= main@%_13_0 (+ main@%_12_0 2)))
                (=> main@verifier.error_0
                    (= main@%_14_0 (= main@%j.0.i.lcssa_1 main@%_13_0)))
                (=> main@verifier.error_0 (not main@%_14_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@_bb main@%j.0.i1_0
                   main@%j.1.v.i_0
                   main@%k.0.i2_0
                   main@%_6_0
                   @__VERIFIER_nondet_int_0)
         true
         (= main@%j.1.i_0 (+ main@%j.0.i1_0 main@%j.1.v.i_0))
         (= main@%k.1.i_0 (+ main@%k.0.i2_0 main@%_6_0))
         (= main@%_8_0 @__VERIFIER_nondet_int_0)
         (= main@%_10_0 (= main@%_9_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_10_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%k.0.i2_1 main@%k.1.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.0.i1_1 main@%j.1.i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%k.0.i2_2 main@%k.0.i2_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.0.i1_2 main@%j.0.i1_1)))
    (main@_bb main@%j.0.i1_2
              main@%j.1.v.i_0
              main@%k.0.i2_2
              main@%_6_0
              @__VERIFIER_nondet_int_0)))
(rule (let ((a!1 (and (main@_bb main@%j.0.i1_0
                          main@%j.1.v.i_0
                          main@%k.0.i2_0
                          main@%_6_0
                          @__VERIFIER_nondet_int_0)
                true
                (= main@%j.1.i_0 (+ main@%j.0.i1_0 main@%j.1.v.i_0))
                (= main@%k.1.i_0 (+ main@%k.0.i2_0 main@%_6_0))
                (= main@%_8_0 @__VERIFIER_nondet_int_0)
                (= main@%_10_0 (= main@%_9_0 0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@_bb_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0) main@%_10_0)
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%k.1.i.lcssa_0 main@%k.1.i_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%j.1.i.lcssa_0 main@%j.1.i_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%k.1.i.lcssa_1 main@%k.1.i.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%j.1.i.lcssa_1 main@%j.1.i.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%k.0.i.lcssa_0 main@%k.1.i.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%j.1.i.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%k.0.i.lcssa_1 main@%k.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_11_0 (= main@%k.0.i.lcssa_1 0)))
                (=> main@verifier.error_0 (not main@%_11_0))
                (=> main@verifier.error_0
                    (= main@%_12_0 (* main@%k.0.i.lcssa_1 2)))
                (=> main@verifier.error_0 (= main@%_13_0 (+ main@%_12_0 2)))
                (=> main@verifier.error_0
                    (= main@%_14_0 (= main@%j.0.i.lcssa_1 main@%_13_0)))
                (=> main@verifier.error_0 (not main@%_14_0))
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

