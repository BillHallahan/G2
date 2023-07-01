(set-info :original "/tmp/sea-zLKTAc/05.pp.ms.o.bc")
(set-info :authors "SeaHorn v.0.1.0-rc3")
(declare-rel verifier.error (Bool Bool Bool ))
(declare-rel main@entry (Int ))
(declare-rel main@_bb (Int Int Int Int Int Int ))
(declare-rel main@verifier.error.split ())
(declare-var main@%_14_0 Bool )
(declare-var main@%_10_0 Int )
(declare-var main@%_11_0 Int )
(declare-var main@%_12_0 Int )
(declare-var main@%_13_0 Bool )
(declare-var main@%..i.lcssa_1 Int )
(declare-var main@%.lcssa_1 Int )
(declare-var main@%not..i_0 Bool )
(declare-var main@%i.0.i4_2 Int )
(declare-var main@%j.0.i3_2 Int )
(declare-var main@%x.0.i2_2 Int )
(declare-var main@%y.0.i1_2 Int )
(declare-var main@%_0_0 Int )
(declare-var main@%_2_0 Int )
(declare-var main@%_3_0 Int )
(declare-var main@%_4_0 Bool )
(declare-var @__VERIFIER_nondet_int_0 Int )
(declare-var main@entry_0 Bool )
(declare-var main@%_1_0 Int )
(declare-var main@.lr.ph_0 Bool )
(declare-var main@%_5_0 Int )
(declare-var main@_bb_0 Bool )
(declare-var main@%i.0.i4_0 Int )
(declare-var main@%j.0.i3_0 Int )
(declare-var main@%x.0.i2_0 Int )
(declare-var main@%y.0.i1_0 Int )
(declare-var main@%i.0.i4_1 Int )
(declare-var main@%j.0.i3_1 Int )
(declare-var main@%x.0.i2_1 Int )
(declare-var main@%y.0.i1_1 Int )
(declare-var main@verifier.error_0 Bool )
(declare-var main@%i.0.i.lcssa_0 Int )
(declare-var main@%j.0.i.lcssa_0 Int )
(declare-var main@%i.0.i.lcssa_1 Int )
(declare-var main@%j.0.i.lcssa_1 Int )
(declare-var main@verifier.error.split_0 Bool )
(declare-var main@%_7_0 Int )
(declare-var main@%_8_0 Int )
(declare-var main@%_9_0 Int )
(declare-var main@%..i_0 Int )
(declare-var main@_bb_1 Bool )
(declare-var main@verifier.error.loopexit_0 Bool )
(declare-var main@%..i.lcssa_0 Int )
(declare-var main@%.lcssa_0 Int )
(rule (verifier.error false false false))
(rule (verifier.error false true true))
(rule (verifier.error true false true))
(rule (verifier.error true true true))
(rule (main@entry @__VERIFIER_nondet_int_0))
(rule (let ((a!1 (=> main@.lr.ph_0 (= main@%not..i_0 (not (= main@%_1_0 0))))))
(let ((a!2 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@.lr.ph_0 (and main@.lr.ph_0 main@entry_0))
                (=> (and main@.lr.ph_0 main@entry_0) (not main@%_4_0))
                a!1
                (=> main@.lr.ph_0 (= main@%_5_0 (ite main@%not..i_0 1 0)))
                (=> main@_bb_0 (and main@_bb_0 main@.lr.ph_0))
                main@_bb_0
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%i.0.i4_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%j.0.i3_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%x.0.i2_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0) (= main@%y.0.i1_0 0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%i.0.i4_1 main@%i.0.i4_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%j.0.i3_1 main@%j.0.i3_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%x.0.i2_1 main@%x.0.i2_0))
                (=> (and main@_bb_0 main@.lr.ph_0)
                    (= main@%y.0.i1_1 main@%y.0.i1_0)))))
  (=> a!2
      (main@_bb main@%x.0.i2_1
                main@%y.0.i1_1
                main@%i.0.i4_1
                main@%_5_0
                main@%j.0.i3_1
                @__VERIFIER_nondet_int_0)))))
(rule (let ((a!1 (and (main@entry @__VERIFIER_nondet_int_0)
                true
                (= main@%_0_0 @__VERIFIER_nondet_int_0)
                (= main@%_2_0 @__VERIFIER_nondet_int_0)
                (= main@%_4_0 (= main@%_3_0 0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@entry_0))
                (=> (and main@verifier.error_0 main@entry_0) main@%_4_0)
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%i.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_0 0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%i.0.i.lcssa_1 main@%i.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@entry_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_14_0 (< main@%j.0.i.lcssa_1 main@%i.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_14_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(rule (=> (and (main@_bb main@%x.0.i2_0
                   main@%y.0.i1_0
                   main@%i.0.i4_0
                   main@%_5_0
                   main@%j.0.i3_0
                   @__VERIFIER_nondet_int_0)
         true
         (= main@%_7_0 (+ main@%x.0.i2_0 1))
         (= main@%_8_0 (+ main@%y.0.i1_0 1))
         (= main@%_9_0 (+ main@%i.0.i4_0 main@%_7_0))
         (= main@%_10_0 (+ main@%_8_0 main@%_5_0))
         (= main@%..i_0 (+ main@%_10_0 main@%j.0.i3_0))
         (= main@%_11_0 @__VERIFIER_nondet_int_0)
         (= main@%_13_0 (= main@%_12_0 0))
         (=> main@_bb_1 (and main@_bb_1 main@_bb_0))
         main@_bb_1
         (=> (and main@_bb_1 main@_bb_0) (not main@%_13_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%i.0.i4_1 main@%_9_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.0.i3_1 main@%..i_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.0.i2_1 main@%_7_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.0.i1_1 main@%_8_0))
         (=> (and main@_bb_1 main@_bb_0) (= main@%i.0.i4_2 main@%i.0.i4_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%j.0.i3_2 main@%j.0.i3_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%x.0.i2_2 main@%x.0.i2_1))
         (=> (and main@_bb_1 main@_bb_0) (= main@%y.0.i1_2 main@%y.0.i1_1)))
    (main@_bb main@%x.0.i2_2
              main@%y.0.i1_2
              main@%i.0.i4_2
              main@%_5_0
              main@%j.0.i3_2
              @__VERIFIER_nondet_int_0)))
(rule (let ((a!1 (and (main@_bb main@%x.0.i2_0
                          main@%y.0.i1_0
                          main@%i.0.i4_0
                          main@%_5_0
                          main@%j.0.i3_0
                          @__VERIFIER_nondet_int_0)
                true
                (= main@%_7_0 (+ main@%x.0.i2_0 1))
                (= main@%_8_0 (+ main@%y.0.i1_0 1))
                (= main@%_9_0 (+ main@%i.0.i4_0 main@%_7_0))
                (= main@%_10_0 (+ main@%_8_0 main@%_5_0))
                (= main@%..i_0 (+ main@%_10_0 main@%j.0.i3_0))
                (= main@%_11_0 @__VERIFIER_nondet_int_0)
                (= main@%_13_0 (= main@%_12_0 0))
                (=> main@verifier.error.loopexit_0
                    (and main@verifier.error.loopexit_0 main@_bb_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0) main@%_13_0)
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%..i.lcssa_0 main@%..i_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa_0 main@%_9_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%..i.lcssa_1 main@%..i.lcssa_0))
                (=> (and main@verifier.error.loopexit_0 main@_bb_0)
                    (= main@%.lcssa_1 main@%.lcssa_0))
                (=> main@verifier.error_0
                    (and main@verifier.error_0 main@verifier.error.loopexit_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_0 main@%.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_0 main@%..i.lcssa_1))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%i.0.i.lcssa_1 main@%i.0.i.lcssa_0))
                (=> (and main@verifier.error_0 main@verifier.error.loopexit_0)
                    (= main@%j.0.i.lcssa_1 main@%j.0.i.lcssa_0))
                (=> main@verifier.error_0
                    (= main@%_14_0 (< main@%j.0.i.lcssa_1 main@%i.0.i.lcssa_1)))
                (=> main@verifier.error_0 main@%_14_0)
                (=> main@verifier.error.split_0
                    (and main@verifier.error.split_0 main@verifier.error_0))
                main@verifier.error.split_0)))
  (=> a!1 main@verifier.error.split)))
(query main@verifier.error.split)

