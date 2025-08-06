(set-logic QF_NIA)

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (+ (* x x) (* y y)) 25))
(assert (<= (* x y) 12))
(assert (= (+ x y z) 10))
(assert (>= x 1))
(assert (>= y 1))
(assert (>= z 0))

(check-sat)
(get-model)
(exit)