#lang typed/racket

(require typed/rackunit)
(require "proof.rkt")
(require "definitions.rkt")
(require "lookup.rkt")
(require "equality.rkt")
(require "axioms.rkt")

;; natural number defintions for testing purposes
(define n1 (nat 'x 'unknown-parity 'unknown-value))
(define n2 (nat 'y 'unknown-parity 'unknown-value))
(define n3 (nat 'a 'even 'unknown-value))
(define n4 (nat 'a 'unknown-parity 'unknown-value))
(define n5 (nat 'a 'even 6))

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

;; get-names-from-stmt tests
(check-equal? (get-names-from-stmt (list n1 n2 n3)) '(x y a))

;; var-in-expr tests
(check-equal? (var-in-expr 'a (parse '(+ a (* b 2)))) #t)
(check-equal? (var-in-expr 'b (parse '(+ a (* b 2)))) #t)
(check-equal? (var-in-expr 'c (parse '(+ a (* b 2)))) #f)

;; expr-to-string tests
(check-equal? (expr-to-string (parse '(+ a (* b 2)))) "(+ a (* b 2))")

;; stmt-to-string tests
(check-equal? (stmt-to-string (list n1 n5))
              "\tx: [unknown-parity] [unknown-value]\n\ta: [even] [6]\n")

;; get-node-by-index tests
(check-equal? (get-node-by-index 2 (list root child1 child2))
              (node
               2
               (list
                (nat 'x 'unknown-parity 'unknown-value)
                (nat 'y 'unknown-parity 'unknown-value)
                (nat
                 'a
                 'unknown-parity
                 'unknown-value))
               0
               '(3)
               ""))
(check-equal? (get-node-by-index 0 (list child1 root child2))
              (node
               0
               (list
                (nat 'x 'unknown-parity 'unknown-value)
                (nat
                 'y
                 'unknown-parity
                 'unknown-value))
               -1
               '(1 2)
               ""))
(check-equal? (get-node-by-index 3 (list child1 root child2 child3))
              (node
               3
               (list
                (nat 'x 'unknown-parity 'unknown-value)
                (nat 'y 'unknown-parity 'unknown-value)
                (nat 'a 'even 6))
               2
               '()
               ""))
(check-exn (regexp (regexp-quote "get-node-by-index: node with index '4' not found"))
           (lambda () (get-node-by-index 4 (list child1 root child2))))

;; generate-path tests
(check-equal? (generate-path 0 (list root))
              '((""
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n")))
(check-equal? (generate-path 1 (list child2 child1 root))
              '(("Applying :\n"
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n\ta: [even] [unknown-value]\n")
                (""
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n")))
(check-equal? (generate-path 3 (list root child1 child2 child3))
              '(("Applying :\n"
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n\ta: [even] [6]\n")
                ("Applying :\n"
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n\ta: [unknown-parity] [unknown-value]\n")
                (""
                 .
                 "\tx: [unknown-parity] [unknown-value]\n\ty: [unknown-parity] [unknown-value]\n")))

;; expr-equals? tests
(check-equal? (expr-equals? 1 1) #t)
(check-equal? (expr-equals? 'a 'a) #t)
(check-equal? (expr-equals? 'a 'b) #t)
(check-equal? (expr-equals? '_ 1) #t)
(check-equal? (expr-equals? (parse '(* 2 _)) (parse '(* 2 (+ 4 b)))) #t)
(check-equal? (expr-equals? 'a 1) #f)
(check-equal? (expr-equals? (parse '(+ a b)) (parse '(+ a 2))) #f)
(check-equal? (expr-equals? (parse '(+ (* 2 3) b)) (parse '(+ (* 2 6) b))) #f)

;; parity-equals? tests
(check-equal? (parity-equals? 'even 'even) #t)
(check-equal? (parity-equals? 'odd 'odd) #t)
(check-equal? (parity-equals? 'even 'odd) #f)
(check-equal? (parity-equals? 'even 'unknown-parity) #f)
(check-equal? (parity-equals? 'unknown-parity 'odd) #t)
(check-equal? (parity-equals? 'unknown-parity 'unknown-parity) #t)

;; nat-equals? tests
(check-equal? (nat-equals?
               (nat 'x 'unknown-parity 'unknown-value)
               (nat 'y 'unknown-parity 'unknown-value)) #t)
(check-equal? (nat-equals?
               (nat 'x 'even 'unknown-value)
               (nat 'y 'unknown-parity 'unknown-value)) #f)
(check-equal? (nat-equals?
               (nat 'x 'unknown-parity 'unknown-value)
               (nat 'y 'even 'unknown-value)) #t)
(check-equal? (nat-equals?
               (nat 'x 'unknown-parity 1)
               (nat 'y 'unknown-parity 'unknown-value)) #f)
(check-equal? (nat-equals?
               (nat 'x 'unknown-parity 'unknown-value)
               (nat 'y 'unknown-parity 1)) #t)

;; get-nat-by-name tests
(check-equal? (get-nat-by-name 'x (list n1)) n1)
(check-equal? (get-nat-by-name 'y (list n1 n1 n1 n2 n1)) n2)
(check-exn (regexp (regexp-quote "name not found: 'z'"))
           (lambda () (get-nat-by-name 'z (list n1 n2))))

;; stmt-equals? tests
(check-equal? (stmt-equals? (list n1 n2 n3) (list n4)) #t)
(check-equal? (stmt-equals? (list n1 n2 n5) (list n3 n2)) #t)
(check-equal? (stmt-equals? (list n1 n2 n3) (list n5 n1 n2)) #f)

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

;; even-forward tests
(set-box! curr-index 0)
(set-box! char-value 97)
(check-equal?
 (even-forward
  (list (nat 'x 'unknown-parity (parse '(+ y z)))
        (nat 'y 'even 'unknown-value)
        (nat 'z 'even 'unknown-value)))
 (list
  (nat
   'x
   'unknown-parity
   (binop '+ 'y 'z))
  (nat 'y 'even (binop '* 2 'a))
  (nat
   'a
   'unknown-parity
   'unknown-value)
  (nat 'z 'even 'unknown-value)))
(set-box! curr-index 0)
(set-box! char-value 97)
(check-equal?
 (even-forward
  (even-forward
  (list (nat 'x 'unknown-parity (parse '(+ y z)))
        (nat 'y 'even 'unknown-value)
        (nat 'z 'even 'unknown-value))))
 (list
  (nat
   'x
   'unknown-parity
   (binop '+ 'y 'z))
  (nat 'y 'even (binop '* 2 'a))
  (nat
   'a
   'unknown-parity
   'unknown-value)
  (nat 'z 'even (binop '* 2 'b))
  (nat
   'b
   'unknown-parity
   'unknown-value)))

;; subst tests
(set-box! curr-index 0)
(set-box! char-value 97)
(check-equal?
 (subst
  (list
   (nat
    'x
    'unknown-parity
    (binop '+ 'y 'z))
   (nat 'y 'even (binop '* 2 'a))
   (nat
    'a
    'unknown-parity
    'unknown-value)
   (nat 'z 'even (binop '* 2 'b))
   (nat
    'b
    'unknown-parity
    'unknown-value)))
 (list
  (nat
   'x
   'unknown-parity
   (binop '+ (binop '* 2 'a) 'z))
  (nat 'y 'even (binop '* 2 'a))
  (nat
   'a
   'unknown-parity
   'unknown-value)
  (nat 'z 'even (binop '* 2 'b))
  (nat
   'b
   'unknown-parity
   'unknown-value)))
(set-box! curr-index 0)
(set-box! char-value 97)
(check-equal?
 (subst
  (subst
   (even-forward
    (even-forward
     (list (nat 'x 'unknown-parity (parse '(+ y z)))
           (nat 'y 'even 'unknown-value)
           (nat 'z 'even 'unknown-value))))))
 (list
  (nat
   'x
   'unknown-parity
   (binop
    '+
    (binop '* 2 'a)
    (binop '* 2 'b)))
  (nat 'y 'even (binop '* 2 'a))
  (nat
   'a
   'unknown-parity
   'unknown-value)
  (nat 'z 'even (binop '* 2 'b))
  (nat
   'b
   'unknown-parity
   'unknown-value)))
