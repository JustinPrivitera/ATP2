#lang typed/racket

(require "definitions.rkt")

(define (expr-to-string [e : expr]) : String
  (match e
    [(? symbol? s) (~a s)]
    [(? natural? n) (~a n)]
    [(binop op l r)
     (string-append
      "(" (~a op) " " (expr-to-string l) " " (expr-to-string r) ")")]))

(define (attr-to-string [a : attr]) : String
  (match a
    [(? parity? p) (~a p)]
    [(? expr? e) (expr-to-string e)]
    [_ (error 'attr-to-string "what is this: ~a" a)]))

(define (stmt-to-string [st : stmt]) : String
  (match st
    [(cons (? attr? a) (? attr? b))
     (string-append (attr-to-string a) " ~ " (attr-to-string b))]))

(define (info-to-string [facts : info]) : String
  (match facts
    [(cons first rest)
     (string-append "\t" (stmt-to-string first) (info-to-string rest))]
    ['() ""]))

(provide (all-defined-out))
