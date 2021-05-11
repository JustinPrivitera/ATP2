#lang typed/racket

(require typed/rackunit)
(require "proof.rkt")
(require "definitions.rkt")
(require "lookup.rkt")
(require "equality.rkt")
(require "print.rkt")
(require "axioms.rkt")

;; natural number defintions for testing purposes
(define n1 (stmt 'x 2))
(define n2 (stmt 'y 3))
(define n3 (stmt 'a 'even))
(define n4 (stmt 'a 4))
(define n5 (stmt 'a 5))

;; tree node definitions for testing purposes
(define root (node 0 (list n1 n2) -1 (list 1 2) ""))
(define child1 (node 1 (list n1 n2 n3) 0 '() ""))
(define child2 (node 2 (list n1 n2 n4) 0 '(3) ""))
(define child3 (node 3 (list n1 n2 n5) 2 '() ""))

;; parse test cases
(check-equal? (parse '(+ 2 x)) (binop '+ 2 'x))
(check-equal? (parse '(* (+ a a) (* 2 6)))
              (binop
               '*
               (binop '+ 'a 'a)
               (binop '* 2 6)))
(check-exn (regexp (regexp-quote "bad operand in ':'"))
           (lambda () (parse '(: 2 x))))

;; expr-to-string tests
(check-equal? (expr-to-string (parse '(+ a (* b 2)))) "(+ a (* b 2))")

;; info-to-string tests
(check-equal? (info-to-string (list n1 n5))
              "\tx ~ 2\n\ta ~ 5\n")

;; get-node-by-index tests
(check-equal? (get-node-by-index 2 (list root child1 child2))
              (node
               2
               (list
                (stmt 'x 2)
                (stmt 'y 3)
                (stmt 'a 4))
               0
               '(3)
               ""))
(check-equal? (get-node-by-index 0 (list child1 root child2))
              (node
               0
               (list
                (stmt 'x 2)
                (stmt 'y 3))
               -1
               '(1 2)
               ""))
(check-equal? (get-node-by-index 3 (list child1 root child2 child3))
              (node
               3
               (list
                (stmt 'x 2)
                (stmt 'y 3)
                (stmt 'a 5))
               2
               '()
               ""))
(check-exn (regexp (regexp-quote "get-node-by-index: node with index '4' not found"))
           (lambda () (get-node-by-index 4 (list child1 root child2))))

;; generate-path tests
(check-equal? (generate-path 0 (list root))
              '(("" . "\tx ~ 2\n\ty ~ 3\n")))
(check-equal? (generate-path 1 (list child2 child1 root))
              '(("Applying :\n" . "\ta ~ even\n") ("" . "\tx ~ 2\n\ty ~ 3\n")))
(check-equal? (generate-path 3 (list root child1 child2 child3))
              '(("Applying :\n" . "\ta ~ 5\n")
                ("Applying :\n" . "\ta ~ 4\n")
                ("" . "\tx ~ 2\n\ty ~ 3\n")))

;; expr-equals? tests
(check-equal? (expr-equals? 1 1) #t)
(check-equal? (expr-equals? 'a 'a) #t)
(check-equal? (expr-equals? 'a 'b) #t)
(check-equal? (expr-equals? '_ 1) #t)
(check-equal? (expr-equals? (parse '(* 2 _)) (parse '(* 2 (+ 4 b)))) #t)
(check-equal? (expr-equals? 'a 1) #f)
(check-equal? (expr-equals? (parse '(+ a b)) (parse '(+ a 2))) #f)
(check-equal? (expr-equals? (parse '(+ (* 2 3) b)) (parse '(+ (* 2 6) b))) #f)

;; stmt-equals? tests
(check-equal? (stmt-equals?
               (stmt 'x 2)
               (stmt 'x 2) #f) #t)
(check-equal? (stmt-equals?
               (stmt 'x 2)
               (stmt 'y 2) #t) #f)
(check-equal? (stmt-equals?
               (stmt 'x 'even)
               (stmt 'y 'odd) #f) #f)
(check-equal? (stmt-equals?
               (stmt 'x '_)
               (stmt 'y 'even) #f) #f)
(check-equal? (stmt-equals?
               (stmt 'x 1)
               (stmt 'y 2) #f) #f)

;; info-equals? tests
(check-equal? (info-equals? (list n1 n2 n3) (list n4) #f) #f)
(check-equal? (info-equals? (list n1 n2 n5) (list n1 n2 n5) #f) #t)
(check-equal? (info-equals? (list n1 n2 n3) (list n5 n1 n2) #f) #f)

;; fresh-index tests
(set-box! curr-index 0)
(check-equal? (fresh-index) 0)
(check-equal? (fresh-index) 1)
(check-equal? (fresh-index) 2)
(check-equal? (fresh-index) 3)
(set-box! curr-index 0)
(check-equal? (fresh-index) 0)
(check-equal? (fresh-index) 1)
(check-equal? (fresh-index) 2)
(check-equal? (fresh-index) 3)
(set-box! curr-index 0)

;; double-info tests
(check-equal? (double-info (list (stmt 1 2) (stmt 2 3) (stmt 3 4)))
              (list
               (stmt 1 2)
               (stmt 2 1)
               (stmt 2 3)
               (stmt 3 2)
               (stmt 3 4)
               (stmt 4 3)))

(check-equal? (regular-form (expanded-form (parse '(+ (* a b) 2)))) (binop '+ (binop '* 'a 'b) 2))
