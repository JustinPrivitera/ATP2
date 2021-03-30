#lang typed/racket

(require typed/rackunit)

;; we will deal purely with natural numbers
(define-type Parity (U 'even 'odd 'unknown-parity))

(define-type Expr (U Binop Natural Symbol 'unknown-value))
(struct Binop ([op : Symbol] [left : Expr] [right : Expr])#:transparent)
(struct Nat ([name : Symbol] [parity : Parity] [value : Expr])#:transparent)

(define (valid-op [op : Symbol]) : Symbol
  (if (member op (list '+ '*)) op (error 'parse "bad operand in '~a'" op)))

(define (parse [s : Sexp]) : Expr
  (match s
    [(list (? symbol? op) a b) (Binop (valid-op op) (parse a) (parse b))]
    [(? natural? n) n]
    [(? symbol? s) s]))

(check-equal? (parse '(+ 2 x)) (Binop '+ 2 'x))
(check-equal? (parse '(* (+ a a) (* 2 6)))
              (Binop
               '*
               (Binop '+ 'a 'a)
               (Binop '* 2 6)))
(check-exn (regexp (regexp-quote "bad operand in ':'"))
           (lambda () (parse '(: 2 x))))





