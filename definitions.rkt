#lang typed/racket

;; types
(define-type parity (U 'even 'odd))
(define-type expr (U binop Natural Symbol '_))
(define-type attr (U expr parity))
(define-type info (Listof stmt))
(define-type axiom (Pairof (-> info (Listof info)) String))
;; an axiom is a function that takes an info and produces a new one
;; coupled with a short description

;; predicates
(define-predicate parity? parity)
(define-predicate expr? expr)
(define-predicate attr? attr)
(define-predicate info? info)

;; structs
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)
(struct stmt ([lhs : attr] [rhs : attr])#:transparent) ;; this is a relation
(struct node ;; tree nodes
  ([index : Integer]
   [data : info]
   [parent : Integer] ;; root has -1 parent
   [children : (Listof Integer)]
   [rule : String])#:transparent)

(define STRICT #t)

;; globals
(define curr-index (box 0))
(define char-value (box 97))

;; gets a fresh index for the nodes of the tree
(define (fresh-index) : Integer
  (define res (unbox curr-index))
  (set-box! curr-index (+ res 1))
  res)

;; gets a fresh char for the variables
(define (fresh-char) : Char
  (define res (unbox char-value))
  (set-box! char-value (+ res 1))
  (integer->char res))

(define (clean-up) : Void
  (set-box! curr-index 0)
  (set-box! char-value 97))

(provide (all-defined-out))
