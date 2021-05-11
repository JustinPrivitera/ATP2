#lang typed/racket

;; types
(define-type parity (U 'even 'odd))
(define-type expr (U binop Natural Symbol '_))
(define-type expr-expanded (U binop-ex Natural Symbol))
(define-type attr (U expr parity))
(define-type info (Listof stmt))
(define-type axiom (Pairof (-> info (Listof info)) String))
;; an axiom is a function that takes an info and produces new ones
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
;; expanded form for expressions
(struct expand ([ex : expr-expanded] [index : Integer])#:transparent)
(struct binop-ex ([op : Symbol] [left : expand] [right : expand])#:transparent)

(define STRICT #t)
(define NOT-STRICT #f)
(define NO-INDEX -1)

;; globals
(define curr-index (box 0))
(define char-value (box 97))
; multipurpose index for use where needed (used for identifying sub expressions)
(define se-index (box 0))
(define final-size (box 0))

;; gets a fresh index for the nodes of the tree
(define (fresh-index) : Integer
  (define res (unbox curr-index))
  (set-box! curr-index (+ res 1))
  res)

;; update the iter-index where needed
(define (fresh-se-index) : Integer
  (define res (unbox se-index))
  (set-box! se-index (+ res 1))
  res)

;; reset the iter-index where needed
(define (increment-and-reset-se-index) : Integer
  (define res (unbox se-index))
  (set-box! se-index 0)
  (+ res 1))

;; gets a fresh char for the variables
(define (fresh-char) : Char
  (define res (unbox char-value))
  (set-box! char-value (+ res 1))
  (integer->char res))

(define (clean-up) : Void
  (set-box! curr-index 0)
  (set-box! char-value 97))

(provide (all-defined-out))
