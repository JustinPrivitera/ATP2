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
;; e1 is the conclusion, e2 the current we are testing against
(define (expr-equals? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [('_ _) #t]
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals? a c) (expr-equals? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2)) #t ;; in this case it doesn't matter since I am only using this function to verify if conclusions are correct
                                     #;(equal? s1 s2)]
    [(_ _) #f]))

(define (attr-equals? [cncl : attr] [curr : attr] [strict? : Boolean]) : Boolean
  (match* (cncl curr)
    [((? parity? p1) (? parity? p2)) (equal? p1 p2)]
    [((? parity? p1) _) #f]
    [(_ (? parity? p2)) #f]
    [((? symbol? s1) (? symbol? s2)) (equal? s1 s2)]
    [((? expr? e1) (? expr? e2))
     (if strict? (expr-equals-strict? e1 e2) (expr-equals? e1 e2))]
    [(_ _) #f]))

(define (stmt-equals? [cncl : stmt] [curr : stmt] [strict? : Boolean]) : Boolean
  (match* (cncl curr)
    [((stmt a b) (stmt c d))
     (or
      (and (attr-equals? a c strict?) (attr-equals? b d strict?))
      (and (attr-equals? a d strict?) (attr-equals? b c strict?)))]))

(define (info-equals? [cncl : info] [curr : info] [strict? : Boolean]) : Boolean
  (andmap
   (lambda ([st1 : stmt]) : Boolean
     (ormap
      (lambda ([st2 : stmt]) : Boolean
        (stmt-equals? st1 st2 strict?))
      curr))
   cncl))

(provide (all-defined-out))
