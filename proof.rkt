#lang typed/racket

(require "definitions.rkt")
(require "lookup.rkt")
(require "equality.rkt")
(require "print.rkt")

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

#;(define (var-in-expr [var : Symbol] [ex : expr]) : Boolean
  (match ex
    [(binop _ left right) (or (var-in-expr var left) (var-in-expr var right))]
    [(? symbol? s) (equal? var s)]
    [_ #f]))

;; is e1 contained in e2
(define (expr-in-expr [e1 : expr] [e2 : expr]) : Boolean
  (if (expr-equals-strict? e1 e2)
      #t
      (match e2
        [(binop _ left right) (or (expr-in-expr e1 left) (expr-in-expr e1 right))]
        [_ #f])))

(define (subst-expr [new-sub-expr : expr] [old-sub-expr : expr] [in : expr]) : expr
  (if (expr-equals-strict? old-sub-expr in)
      new-sub-expr
      (match in
        [(binop sym left right)
         (cond
            [(expr-in-expr old-sub-expr left)
             (binop
              sym
              (subst-expr new-sub-expr old-sub-expr left)
              right)]
            [(expr-in-expr old-sub-expr right)
             (binop
              sym
              left
              (subst-expr new-sub-expr old-sub-expr right))]
            [else in])]
        [_ in])))

;; look back through the generated tree, following nodes to their parents,
;; and create a list of the string representations of each node back to the root
(define (generate-path [index : Integer] [tree : (Listof node)]) : (Listof (Pairof String String))
  (define curr (get-node-by-index index tree))
  (define parent (node-parent curr))
  (if (equal? -1 parent)
      (list (cons (node-rule curr) (info-to-string (node-data curr))))
      (append
       (list (cons
              (string-append "Applying " (node-rule curr) ":\n")
              (info-to-string (list (last (node-data curr))))))
       (generate-path parent tree))))

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
         [cncl : info]
         [index : Integer]
         [axioms : (Listof axiom)]
         [tree : (Listof node)]) : (Listof (Pairof String String))
  (if (info-equals? cncl (node-data (get-node-by-index index tree)) #f) ; if we've arrived at our answer
      ; then return the index of this node
      (begin
        (clean-up)
        (generate-path index tree))
      ; otherwise, add new nodes to the tree and continue with the next index
      (reach-conclusion cncl (+ index 1) axioms (apply-axioms index tree axioms))))

;; given a hypothesis, conclusion, and axioms, display the steps of a
;; proof of the conclusion from the hypothesis using the provided axioms
(define (prove
         [assumption : info]
         [conclusion : info]
         [axioms : (Listof axiom)]) : Void
  (clean-up)
  (map
   (lambda ([step : (Pairof String String)]) : Void
     (display
      (string-append
       (~a (fresh-index)) ") " (car step)
       (cdr step)))
     (void))
   (reverse
    (reach-conclusion
     conclusion
     0
     axioms
     (list (node (fresh-index) assumption -1 '() "Given:\n")))))
  (void))

(provide (all-defined-out))
