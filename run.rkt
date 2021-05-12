#lang typed/racket

(require "proof.rkt")
(require "definitions.rkt")
(require "axioms.rkt")
(require "equality.rkt")

(define proofs-to-do (range 21))

(define (prove-theorem
         [asmp : info]
         [cncl : info]
         [words : String]) : Void
  (display words)
  (prove asmp cncl axioms)
  (display "================================\n")
  (void))

;; proof 1 (tests even-forward)
#;(if (member 1 proofs-to-do)
    (prove-theorem
     (list (stmt 'x 'even))
     (list (stmt 'x (parse '(* 2 '_))))
     "Proof 1:\nGiven x even, prove that x = (* 2 a) for some a.\n")
    (void))

;; proof 2 (tests even-forward)
#;(if (member 2 proofs-to-do)
    (prove-theorem
     (list (stmt 'even 'x)
           (stmt 'even 'y))
     (list (stmt 'x (parse '(* 2 '_)))
           (stmt 'y (parse '(* 2 '_))))
     "\nProof 2:\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
    (void))

;; proof 3 (tests even-reverse)
#;(if (member 3 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(* 2 y))))
     (list (stmt 'x 'even))
     "\nProof 3:\nGiven x = (* 2 y) for some y, prove that x is even.\n")
    (void))

;; proof 4 (tests even-reverse and even-forward)
#;(if (member 4 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(* 2 y)))
           (stmt 'z 'even))
     (list (stmt 'x 'even)
           (stmt 'z (parse '(* 2 _))))
     "\nProof 4:\nGiven x = (* 2 y) for some y and z even, prove that x is even and z = (* 2 a) for some a.\n")
    (void))

;; proof 5 (tests even and subst)
(if (member 5 proofs-to-do)
    (prove-theorem
     (list (stmt 'x 'y)
           (stmt 'y (parse '(* 2 z))))
     (list (stmt 'x 'even))
     "\nProof 5:\nGiven x = y and y = (* 2 z) for some z, prove x is even.\n")
    (void))

;; proof 6 (tests even and subst)
#;(if (member 6 proofs-to-do)
    (prove-theorem
     (list (stmt 'x 'y)
           (stmt 'y 'even))
     (list (stmt 'x 'even))
     "\nProof 6:\nGiven x = y and y is even, prove x is even.\n")
    (void))

;; proof 7 (tests factor and even)
(if (member 7 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ (* 2 a) (* 2 b)))))
     (list (stmt 'x 'even))
     "\nProof 7:\nGiven x = (+ (* 2 a) (* 2 b)) for some a and b, prove x is even.\n")
    (void))

#;(if (member 8 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 2))))
     (list (stmt 'x (parse '(+ 2 1))))
     "\nProof 8:\nTBD\n")
    (void))

#;(if (member 9 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (* 2 3)))))
     (list (stmt 'x (parse '(+ (* 3 2) 1))))
     "\nProof 9:\nTBD\n")
    (void))

#;(if (member 10 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 2))))
     (list (stmt 'x (parse 3)))
     "\nProof 10:\nTBD\n")
    (void))

#;(if (member 11 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (* 2 3)))))
     (list (stmt 'x (parse 7)))
     "\nProof 11:\nTBD\n")
    (void))

#;(if (member 12 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ a (* 2 3)))))
     (list (stmt 'x (parse '(+ 6 a))))
     "\nProof 12:\nTBD\n")
    (void))

#;(if (member 13 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(* 1 (* 2 3)))))
     (list (stmt 'x (parse '(* (* 1 2) 3))))
     "\nProof 13:\nTBD\n")
    (void))

#;(if (member 14 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (+ (+ 2 3) 4)))))
     (list (stmt 'x (parse '(+ 1 (+ 2 (+ 3 4))))))
     "\nProof 14:\nTBD\n")
    (void))

#;(if (member 15 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (+ (+ 2 3) 4)))))
     (list (stmt 'x (parse '(+ (+ 1 2) (+ 3 4)))))
     "\nProof 15:\nTBD\n")
    (void))

#;(if (member 16 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (+ (+ 2 3) 4)))))
     (list (stmt 'x (parse '(+ (+ 1 2) (+ 3 4)))))
     "\nProof 15:\nTBD\n")
    (void))

#;(if (member 17 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ 1 (+ (+ 2 3) 4)))))
     (list (stmt 'x (parse '(+ (+ 1 2) (+ 3 4)))))
     "\nProof 15:\nTBD\n")
    (void))

;; proof 8 (tests factor subst and even)
#;(if (member 18 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ y z)))
           (stmt 'y 'even)
           (stmt 'z 'even))
     (list (stmt 'x 'even))
     "\nProof 18:\nGiven x = (+ y z) for some y even and z even, prove x is even.\n")
    (void))

(if (member 19 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ y z)))
           (stmt 'y 'odd)
           (stmt 'y (parse '(+ (* 2 a) 1)))
           (stmt 'z 'even)
           (stmt 'z (parse '(* 2 b)))
           (stmt 'x (parse '(+ (+ (* 2 a) 1) (* 2 b)))))
     (list (stmt 'x (parse '(+ (* 2 _) 1))))
     "\nProof 19:\nGiven x = (+ y z) for some y odd and z even, prove x is odd.\n")
    (void))

(if (member 19 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ y z)))
           (stmt 'y 'odd)
           (stmt 'y (parse '(+ (* 2 a) 1)))
           (stmt 'z 'even)
           (stmt 'z (parse '(* 2 b))))
     (list (stmt 'x (parse '(+ (* 2 _) 1))))
     "\nProof 19:\nGiven x = (+ y z) for some y odd and z even, prove x is odd.\n")
    (void))

#;(if (member 19 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ y z)))
           (stmt 'y 'odd)
           (stmt 'y (parse '(+ (* 2 a) 1)))
           (stmt 'z 'even)
           (stmt 'z (parse '(* 2 b))))
     (list (stmt 'x (parse '(+ (* 2 _) 1))))
     "\nProof 19:\nGiven x = (+ y z) for some y odd and z even, prove x is odd.\n")
    (void))

#;(if (member 20 proofs-to-do)
    (prove-theorem
     (list (stmt 'x (parse '(+ y z)))
           (stmt 'y 'odd)
           (stmt 'z 'odd))
     (list (stmt 'x 'even))
     "\nProof 20:\nGiven x = (+ y z) for some y odd and z odd, prove x is even.\n")
    (void))
