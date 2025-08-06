(set-logic QF_NIA)

(declare-fun x () Int)

(assert (= (+ (* x x) (* 5 x)) -6))
(assert (>= x -10))
(assert (<= x 10))

(check-sat)
(get-model)
(exit)