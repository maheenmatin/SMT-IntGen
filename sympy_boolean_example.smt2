(set-logic QF_LIA)

(declare-fun p () Int)
(declare-fun q () Int)
(declare-fun r () Int)

(assert (or (< r 0) (and (> p 0) (> q 0))))
(assert (= (+ p q r) 0))

(check-sat)
(get-model)
(exit)