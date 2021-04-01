#lang typed/racket

(require "proof.rkt")

;; axioms

;; axiom 1 helper
(define (even-forward-helper
         [st : stmt]
         [var-name : Symbol]
         [done-already? : Boolean]) : (Listof Any)
  (define done? (box done-already?))
  (match st
    [(cons first rest)
     (cons
      (if
       (and (not done-already?)
            (equal? (nat-par first) 'even)
            (equal? (nat-value first) 'unknown-value))
       (begin
         (set-box! done? #t)
         (list
          (nat (nat-name first) (nat-par first) (binop '* 2 var-name))
          (nat var-name 'unknown-parity 'unknown-value)))
       first)
      (even-forward-helper rest var-name (unbox done?)))]
    ['() '()]))

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [st : stmt]) : (U stmt Void)
  (if ;; if the axiom is applicable
   (match st
     ['() #f]
     [_ (ormap
         (lambda ([n : nat]) : Boolean
           (and (equal? (nat-par n) 'even) (equal? (nat-value n) 'unknown-value)))
         st)])
   (cast (flatten (even-forward-helper st (string->symbol (~a (fresh-char))) #f)) stmt)
   (void)))

(define axioms (list even-forward))

(define hypo (box (list (nat 'x 'even 'unknown-value))))
(define cncl (box (list (nat 'x 'even (parse '(* 2 a))))))
(display "Given x even, prove that x = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)

(set-box! hypo (list (nat 'x 'even 'unknown-value)
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even (parse '(* 2 a)))
                     (nat 'y 'even (parse '(* 2 b)))))
(display "\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
(prove (unbox hypo) (unbox cncl) axioms)
