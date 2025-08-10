; x + y = 10
; 2*x - 3*y = 5
; x**2 + y**2 = 25
; z % 2 = 0

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

(assert (= (+ x y) 10))
(assert (= (+ (* -3 y) (* 2 x)) 5))
(assert (= (+ (* x x) (* y y)) 25))
(assert (= (mod z 2) 0))
