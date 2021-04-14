#lang typed/racket

;; get old proofs working
;; then add new ones taking advantage of new framework

(require "proof.rkt")
(require "definitions.rkt")
(require "axioms.rkt")

#;(define proofs-to-do '(1 2 3 4 5 6 7 8))
(define proofs-to-do '(1 2))

(define (prove-theorem
         [asmp : info]
         [cncl : info]
         [words : String]) : Void
  (display words)
  (prove asmp cncl axioms)
  (display "================================\n")
  (void))

;; proof 1 (tests even-forward)
(if (member 1 proofs-to-do)
    (prove-theorem
     (list (stmt 'x 'even))
     (list (stmt 'x (parse '(* 2 '_))))
     "Proof 1:\nGiven x even, prove that x = (* 2 a) for some a.\n")
    (void))

;; proof 2 (tests even-forward)
(if (member 2 proofs-to-do)
    (prove-theorem
     (list (stmt 'x 'even)
           (stmt 'y 'even))
     (list (stmt 'x (parse '(* 2 '_)))
           (stmt 'y (parse '(* 2 '_))))
     "\nProof 2:\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
    (void))

;; proof 1 (tests even-forward)
(if (member 1 proofs-to-do)
    (prove-theorem
     (list (stmt 'even 'x))
     (list (stmt 'x (parse '(* 2 '_))))
     "Proof 1:\nGiven x even, prove that x = (* 2 a) for some a.\n")
    (void))

;; proof 2 (tests even-forward)
(if (member 2 proofs-to-do)
    (prove-theorem
     (list (stmt 'even 'x)
           (stmt 'even 'y))
     (list (stmt 'x (parse '(* 2 '_)))
           (stmt 'y (parse '(* 2 '_))))
     "\nProof 2:\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
    (void))
#|
;; proof 3 (tests even-reverse)
(if (member 3 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse '(* 2 y)))
           (nat 'y 'unknown-parity 'unknown-value))
     (list (nat 'x 'even '_))
     "\nProof 3:\nGiven x = (* 2 y) for some y, prove that x is even.\n")
    (void))

;; proof 4 (tests even-reverse and even-forward)
(if (member 4 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse '(* 2 y)))
           (nat 'y 'unknown-parity 'unknown-value)
           (nat 'z 'even 'unknown-value))
     (list (nat 'x 'even '_)
           (nat 'z 'even (parse '(* 2 _))))
     "\nProof 4:\nGiven x = (* 2 y) for some y and z even, prove that x is even and z = (* 2 a) for some a.\n")
    (void))

;; proof 5 (tests even and subst)
(if (member 5 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse 'y))
           (nat 'y 'unknown-parity (parse '(* 2 z)))
           (nat 'z 'unknown-parity 'unknown-value))
     (list (nat 'x 'even '_))
     "\nProof 5:\nGiven x = y and y = (* 2 z) for some z, prove x is even.\n")
    (void))

;; proof 6 (tests even and subst)
(if (member 6 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse 'y))
           (nat 'y 'even 'unknown-value))
     (list (nat 'x 'even '_))
     "\nProof 6:\nGiven x = y and y is even, prove x is even.\n")
    (void))

;; proof 7 (tests factor and even)
(if (member 7 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse '(+ (* 2 a) (* 2 b))))
           (nat 'a 'unknown-parity 'unknown-value)
           (nat 'b 'unknown-parity 'unknown-value))
     (list (nat 'x 'even '_))
     "\nProof 7:\nGiven x = (+ (* 2 a) (* 2 b)) for some a and b, prove x is even.\n")
    (void))

;; proof 8 (tests factor subst and even)
(if (member 8 proofs-to-do)
    (prove-theorem
     (list (nat 'x 'unknown-parity (parse '(+ y z)))
           (nat 'y 'even 'unknown-value)
           (nat 'z 'even 'unknown-value))
     (list (nat 'x 'even (parse '_)))
     "\nProof 8:\nGiven x = (+ y z) for some y even and z even, prove x is even.\n")
    (void))
|#