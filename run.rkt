#lang typed/racket

(require "proof.rkt")
(require "definitions.rkt")
(require "axioms.rkt")

;; proof 1
(define hypo (box (list (nat 'x 'even 'unknown-value))))
(define cncl (box (list (nat 'x 'even (parse '(* 2 a))))))
(display "Proof 1:\nGiven x even, prove that x = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 2
(set-box! hypo (list (nat 'x 'even 'unknown-value)
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even (parse '(* 2 a)))
                     (nat 'y 'even (parse '(* 2 b)))))
(display "\nProof 2:\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 3
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 3:\nGiven x = (* 2 y) for some y, prove that x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 4
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)
                     (nat 'z 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)
                     (nat 'z 'even (parse '(* 2 _)))))
(display "\nProof 4:\nGiven x = (* 2 y) for some y and z even, prove that x is even and z = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 5
(set-box! hypo (list (nat 'x 'unknown-parity (parse 'y))
                     (nat 'y 'unknown-parity (parse '(* 2 z)))
                     (nat 'z 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 5:\nGiven x = y and y = (* 2 z) for some z, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 6
(set-box! hypo (list (nat 'x 'unknown-parity (parse 'y))
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 6:\nGiven x = y and y is even, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 7
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(+ (* 2 a) (* 2 b))))
                     (nat 'a 'unknown-parity 'unknown-value)
                     (nat 'a 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 7:\nGiven x = (+ (* 2 a) (* 2 b)) for some a and b, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")
