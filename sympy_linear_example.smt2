(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (+ x (* 2 y)) 10))
(assert (>= (+ (* -1 y) (* 3 x)) 5))
(assert (> x 0))
(assert (>= y 0))

(check-sat)
(get-model)
(exit)