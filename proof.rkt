#lang typed/racket

(require typed/rackunit)

;; we will deal purely with natural numbers
(define-type parity (U 'even 'odd 'unknown-parity))
(define-type expr (U binop Natural Symbol 'unknown-value))
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)
(struct nat ([name : Symbol] [par : parity] [value : expr])#:transparent)
(define-type stmt (Listof nat)) ; a statement of truth about specific natural numbers

(define (valid-op [op : Symbol]) : Symbol
  (if (member op (list '+ '*)) op (error 'parse "bad operand in '~a'" op)))

(define (parse [s : Sexp]) : expr
  (match s
    [(list (? symbol? op) a b) (binop (valid-op op) (parse a) (parse b))]
    [(? natural? n) n]
    [(? symbol? s) s]))

;; non-strict
(define (expr-equals? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals? a c) (expr-equals? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2))
     (equal? s1 s2)]
    [('unknown-value _) #t]
    [(_ _) #f]))

;; non-strict
(define (parity-equals? [p1 : parity] [p2 : parity]) : Boolean
  (or (equal? p1 'unknown-parity) (equal? p1 p2)))

;; does not take into account the name
(define (nat-equals? [n1 : nat] [n2 : nat]) : Boolean
  (match* (n1 n2)
    [((nat _ par1 val1) (nat _ par2 val2))
     (and (parity-equals? par1 par2) (expr-equals? val1 val2))]))

(define (get-nat-by-name [name : Symbol] [curr : stmt]) : nat
  (match curr
    [(cons (nat curr-name par val) rest)
     (if (equal? name curr-name)
         (nat curr-name par val)
         (get-nat-by-name name rest))]
    ['() (error 'get-nat-by-name "name not found: '~a'" name)]))

;; takes a current statement of truth and a conclusion
;; and determines if the conclusion is reached by the
;; statement
(define (stmt-equals? [curr : stmt] [cncl : stmt]) : Boolean
  (andmap
   (lambda ([n : nat]) : Boolean
     (nat-equals? n (get-nat-by-name (nat-name n) curr))) cncl))

;;;;;;;;;;;;;;;;;TEST CASES;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; natural number defintions for testing purposes
(define n1 (nat 'x 'unknown-parity 'unknown-value))
(define n2 (nat 'y 'unknown-parity 'unknown-value))
(define n3 (nat 'a 'even 'unknown-value))
(define n4 (nat 'a 'unknown-parity 'unknown-value))
(define n5 (nat 'a 'even 6))

;; parse test cases
(check-equal? (parse '(+ 2 x)) (binop '+ 2 'x))
(check-equal? (parse '(* (+ a a) (* 2 6)))
              (binop
               '*
               (binop '+ 'a 'a)
               (binop '* 2 6)))
(check-exn (regexp (regexp-quote "bad operand in ':'"))
           (lambda () (parse '(: 2 x))))

;; expr-equals? tests
(check-equal? (expr-equals? 1 1) #t)
(check-equal? (expr-equals? 'a 'a) #t)
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
