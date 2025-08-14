; -6*e**3*d**3*b**3 = 10
; -7*b**3*c**3 - 7*d**3*a**2*e**3 + 5*c**3*e**3*a**2 + 5*d + 3*d = -1
; 5*e + 6*d**2*c**2*a**2 + 7*a**2*e**2*d**2 + 5*e**3*d**3*a**3 - 5*a**2*b**2*e**3 = 5*e**3*b**3*a**2
; -6*e**2*c**2 + 7*d - 6*d**3*a**2 - 6*d**3*b**2*a**3 = 8

(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(declare-const e Int)

(assert (= (* -6 (* b (* b b)) (* d (* d d)) (* e (* e e))) 10))
(assert (= (+ (* 8 d) (* -7 (* b (* b b)) (* c (* c c))) (* -7 (* a a) (* d (* d d)) (* e (* e e))) (* 5 (* a a) (* c (* c c)) (* e (* e e)))) -1))
(assert (= (+ (* 5 e) (* -5 (* a a) (* b b) (* e (* e e))) (* 5 (* a (* a a)) (* d (* d d)) (* e (* e e))) (* 6 (* a a) (* c c) (* d d)) (* 7 (* a a) (* d d) (* e e))) (* 5 (* a a) (* b (* b b)) (* e (* e e)))))
(assert (= (+ (* 7 d) (* -6 (* a a) (* d (* d d))) (* -6 (* c c) (* e e)) (* -6 (* a (* a a)) (* b b) (* d (* d d)))) 8))
