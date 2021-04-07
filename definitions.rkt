#lang typed/racket

;; we will deal purely with natural numbers
(define-type parity (U 'even 'odd 'unknown-parity))
(define-type expr (U binop Natural Symbol 'unknown-value '_))
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)

;; a definition for a natural number
(struct nat ([name : Symbol] [par : parity] [value : expr])#:transparent)
(define-type stmt (Listof nat)) ; a statement of truth about specific natural numbers

;; an axiom is a function that takes a statement of truth and produces a new one
;; in the case of an axiom that is unable to be applied, the axiom will return void
(define-type axiom (-> stmt stmt))

;; nodes for the tree
(struct node
  ([index : Integer]
   [data : stmt]
   [parent : Integer] ;; root has -1 parent
   [children : (Listof Integer)])#:transparent)

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

(provide (all-defined-out))
