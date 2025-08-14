; 7*a**3*c**2*e**3 + 6*c**2*a**2*e**3 + 7*a**3*d**2 = 2
; -7*a**3*b**3*d**2 - 7*c**3*a**2 + 7*c**2*e**2 = -2 - 7*e + 2*e**3*c**3
; 5*a**3*e**3*d**2 + 5*c*d - 5*c**3*e**3 = -11
; 7*d**2*a**2*e**3 + 4*c**2*a**2*b**2 + 7*e - 6*c**3*e**3*d**3 + 6*b**3*d**3*c**3 = 12

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)

(assert (= (+ (* 7 (* a (* a a)) (* d d)) (* 6 (* a a) (* c c) (* e (* e e))) (* 7 (* a (* a a)) (* c c) (* e (* e e)))) 2))
(assert (= (+ (* -7 (* a a) (* c (* c c))) (* 7 (* c c) (* e e)) (* -7 (* a (* a a)) (* b (* b b)) (* d d))) (+ -2 (* -7 e) (* 2 (* c (* c c)) (* e (* e e))))))
(assert (= (+ (* -5 (* c (* c c)) (* e (* e e))) (* 5 c d) (* 5 (* a (* a a)) (* d d) (* e (* e e)))) -11))
(assert (= (+ (* 7 e) (* -6 (* c (* c c)) (* d (* d d)) (* e (* e e))) (* 4 (* a a) (* b b) (* c c)) (* 6 (* b (* b b)) (* c (* c c)) (* d (* d d))) (* 7 (* a a) (* d d) (* e (* e e)))) 12))
