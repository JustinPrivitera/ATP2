#lang typed/racket

;; we will deal purely with natural numbers
(define-type parity (U 'even 'odd))
(define-type expr (U binop Natural Symbol '_))
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)

(define-type attr (U expr parity))
(define-type stmt (Pairof attr attr)) ;; this is a relation
(define-type info (Listof stmt))

(define-predicate parity? parity)
(define-predicate expr? expr)
(define-predicate attr? attr)
(define-predicate stmt? stmt)
(define-predicate info? info)

;; an axiom is a function that takes a statement of truth and produces a new one
;; in the case of an axiom that is unable to be applied, the axiom will return void
(define-type axiom (Pairof (-> info info) String))

;; nodes for the tree
(struct node
  ([index : Integer]
   [data : info]
   [parent : Integer] ;; root has -1 parent
   [children : (Listof Integer)]
   [rule : String])#:transparent)

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
