#lang typed/racket

(require "definitions.rkt")
(require "lookup.rkt")
(require "equality.rkt")

;; default values for structs???
;; add quantifiers
;; it might be nice to have a place where all the names live so I don't steal one that's in use
;; make axioms more general; an axiom can take predicates that specify what it is
;;   so an axiom could check if it was applicable to a natural number
;;   and then have steps for applying it

;; is the provided operator valid
(define (valid-op [op : Symbol]) : Symbol
  (if (member op (list '+ '*)) op (error 'parse "bad operand in '~a'" op)))

;; parse a given s-expression into an expr
(define (parse [s : Sexp]) : expr
  (match s
    [(list (? symbol? op) a b) (binop (valid-op op) (parse a) (parse b))]
    [(? natural? n) n]
    [(? symbol? s) s]
    [_ '_]))

(define (var-in-expr [var : Symbol] [ex : expr]) : Boolean
  (match ex
    [(binop _ left right) (or (var-in-expr var left) (var-in-expr var right))]
    [(? symbol? s) (equal? var s)]
    [_ #f]))

;; given a variable name and its value, substitute it's value in a given expression
(define (subst-var [var-name : Symbol] [value : expr] [ex : expr]) : expr
  (match ex
    [(binop sym left right)
     (binop
      sym
      (subst-var var-name value left)
      (subst-var var-name value right))]
    [(? natural? n) n]
    [(? symbol? s) (if (equal? s var-name) value s)]))

(define (expr-to-string [e : expr]) : String
  (match e
    [(? symbol? s) (~a s)]
    [(? natural? n) (~a n)]
    [(binop op l r)
     (string-append
      "(" (~a op) " " (expr-to-string l) " " (expr-to-string r) ")")]))

(define (stmt-to-string [st : stmt]) : String
  (match st
    [(cons (nat name par val) rest)
     (string-append
      "\t" (~a name) ": [" (~a par) "] [" (expr-to-string val) "]\n"
      (stmt-to-string rest))]
    ['() ""]))

;; look back through the generated tree, following nodes to their parents,
;; and create a list of the string representations of each node back to the root
(define (generate-path [index : Integer] [tree : (Listof node)]) : (Listof String)
  (define curr (get-node-by-index index tree))
  (define parent (node-parent curr))
  (if (equal? -1 parent)
      (list (stmt-to-string (node-data curr)))
      (append (list (stmt-to-string (node-data curr))) (generate-path parent tree))))

; get current node
; go through axioms
; if any can be applied, then apply them, creating children
; create a new node for parent with the children included
; use get-all-from-except and append the new parent with children
; return the new tree
(define (apply-axioms
         [index : Integer]
         [tree : (Listof node)]
         [axioms : (Listof axiom)]) : (Listof node)
  ;; get the new parent
  (define curr (get-node-by-index index tree))
  ;; generate the children
  (define children
    (map
     (lambda ([ax : axiom]) : node
       (node (fresh-index) ((car ax) (node-data curr)) index '() (cdr ax)))
     axioms))
  ;; collect everything in a new tree
  (append
   ;; get all the untouched nodes
   (get-all-from-except tree index)
   ;; add the children's indicies to the parent
   (list
    (node
     (node-index curr)
     (node-data curr)
     (node-parent curr)
     (map
      (lambda ([child : node]) : Integer
        (node-index child))
      children)
     (node-rule curr)))
   ;; and add the children themselves
   children))

;; returns the path to the node that is equivalent to the conclusion
(define (reach-conclusion
         [cncl : stmt]
         [index : Integer]
         [axioms : (Listof axiom)]
         [tree : (Listof node)]) : (Listof String)
  (if (stmt-equals? (node-data (get-node-by-index index tree)) cncl) ; if we've arrived at our answer
      ; then return the index of this node
      (begin
        (set-box! curr-index 0)
        (generate-path index tree))
      ; otherwise, add new nodes to the tree and continue with the next index
      (reach-conclusion cncl (+ index 1) axioms (apply-axioms index tree axioms))))

;; given a hypothesis, conclusion, and axioms, display the steps of a
;; proof of the conclusion from the hypothesis using the provided axioms
(define (prove
         [hypothesis : stmt]
         [conclusion : stmt]
         [axioms : (Listof axiom)]) : Void
  (set-box! curr-index 0)
  (set-box! char-value 97)
  (map
   (lambda ([step : String]) : Void
     (display
      (string-append
       "Step " (~a (fresh-index)) ":\n"
       step))
     (void))
   (reverse
    (reach-conclusion
     conclusion
     0
     axioms
     (list (node (fresh-index) hypothesis -1 '() "Given")))))
  (void))

(provide (all-defined-out))
