#lang typed/racket

(require "definitions.rkt")
(require "lookup.rkt")

(define (expr-equals-strict? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals-strict? a c) (expr-equals-strict? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2))
     (equal? s1 s2)]))

;; non-strict
;; e1 is the conclusion, e2 the current
(define (expr-equals? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [('_ _) #t]
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals? a c) (expr-equals? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2)) #t ;; in this case it doesn't matter since I am only using this function to verify if conclusions are correct
     #;(equal? s1 s2)]
    [('unknown-value _) #t]
    [(_ _) #f]))

;; non-strict
(define (parity-equals? [p1 : parity] [p2 : parity]) : Boolean
  (or (equal? p1 'unknown-parity) (equal? p1 p2)))

;; does not take into account the name
;; n1 is the conclusion n2 is the current
(define (nat-equals? [n1 : nat] [n2 : nat]) : Boolean
  (match* (n1 n2)
    [((nat _ par1 val1) (nat _ par2 val2))
     (and (parity-equals? par1 par2) (expr-equals? val1 val2))]))

;; takes a current statement of truth and a conclusion
;; and determines if the conclusion is reached by the
;; statement
(define (stmt-equals? [curr : stmt] [cncl : stmt]) : Boolean
  (andmap
   (lambda ([n : nat]) : Boolean
     (nat-equals? n (get-nat-by-name (nat-name n) curr)))
   cncl))

(provide (all-defined-out))
