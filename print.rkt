#lang typed/racket

(require "definitions.rkt")

(define (expr-to-string [e : expr]) : String
  (match e
    [(? symbol? s) (~a s)]
    [(? natural? n) (~a n)]
    [(binop op l r)
     (string-append
      "(" (~a op) " " (expr-to-string l) " " (expr-to-string r) ")")]))

(define (stmt-to-string [st : stmt]) : String
  (match st
    [(stmt (? parity? a) (? expr? b))
     (string-append (expr-to-string b) " is " (~a a) "\n")]
    [(stmt (? expr? a) (? parity? b))
     (string-append (expr-to-string a) " is " (~a b) "\n")]
    [(stmt (? expr? a) (? expr? b))
     (string-append (expr-to-string a) " = " (expr-to-string b) "\n")]
    [_ (error 'stmt-to-string "what is this: ~a" st)]))

(define (info-to-string [facts : info]) : String
  (match facts
    [(cons first rest)
     (string-append "\t" (stmt-to-string first) (info-to-string rest))]
    ['() ""]))

(provide (all-defined-out))
