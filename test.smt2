
(declare-const x Real)
(assert (> x 0))
(assert (> 1 x))

(check-sat)
(get-model)