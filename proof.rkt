#lang typed/racket

;; default values for structs???
;; add quantifiers
;; it might be nice to have a place where all the names live so I don't steal one that's in use
;; make axioms more general; an axiom can take predicates that specify what it is

;; we will deal purely with natural numbers
(define-type parity (U 'even 'odd 'unknown-parity))
(define-type expr (U binop Natural Symbol 'unknown-value '_))
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)

;; a definition for a natural number
(struct nat ([name : Symbol] [par : parity] [value : expr])#:transparent)
(define-type stmt (Listof nat)) ; a statement of truth about specific natural numbers

;; an axiom is a function that takes a statement of truth and produces a new one
;; in the case of an axiom that is unable to be applied, the axiom will return void
(define-type axiom (-> stmt (U stmt Void)))

;; nodes for the tree
(struct node
  ([index : Integer]
   [data : stmt]
   [parent : Integer] ;; root has -1 parent
   [children : (Listof Integer)])#:transparent)

(define curr-index (box 0))
(define char-value (box 97))

;; is the provided operator valid
(define (valid-op [op : Symbol]) : Symbol
  (if (member op (list '+ '*)) op (error 'parse "bad operand in '~a'" op)))

;; parse a given s-expression into an expr
(define (parse [s : Sexp]) : expr
  (match s
    [(list (? symbol? op) a b) (binop (valid-op op) (parse a) (parse b))]
    [(? natural? n) n]
    [(? symbol? s) s]))

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

(define (get-node-by-index [index : Integer] [nodes : (Listof node)]) : node
  (match nodes
    [(cons first rest)
     (if (equal? index (node-index first))
         first
         (get-node-by-index index rest))]
    ['() (error 'get-node-by-index "node with index '~a' not found" index)]))

;; look back through the generated tree, following nodes to their parents,
;; and create a list of the string representations of each node back to the root
(define (generate-path [index : Integer] [tree : (Listof node)]) : (Listof String)
  (define curr (get-node-by-index index tree))
  (define parent (node-parent curr))
  (if (equal? -1 parent)
      (list (stmt-to-string (node-data curr)))
      (append (list (stmt-to-string (node-data curr))) (generate-path parent tree))))

;; non-strict
;; e1 is the conclusion, e2 the current
(define (expr-equals? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [('_ _) #t]
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals? a c) (expr-equals? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2)) #t ;; in this case it doesn't matter since I am only using this function to verify if conclusions are correct
     #;(equal? s1 s2)]
    [('unknown-value _) #t]
    [(_ _) #f]))

;; non-strict
(define (parity-equals? [p1 : parity] [p2 : parity]) : Boolean
  (or (equal? p1 'unknown-parity) (equal? p1 p2)))

;; does not take into account the name
;; n1 is the conclusion n2 is the current
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
     (nat-equals? n (get-nat-by-name (nat-name n) curr)))
   cncl))

;; get all the nodes in the tree except the node with the specified index
(define (get-all-from-except [tree : (Listof node)] [index : Integer]) : (Listof node)
  (match tree
    [(cons first rest)
     (if (equal? (node-index first) index)
         (get-all-from-except rest index)
         (append (list first) (get-all-from-except rest index)))]
    ['() '()]))

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

;; removes nodes that have -1 as their index
(define (cull-bad-nodes [nodes : (Listof node)]) : (Listof node)
  (match nodes
    [(cons first rest)
     (if (equal? -1 (node-index first))
         (cull-bad-nodes rest)
         (cons first (cull-bad-nodes rest)))]
    ['() '()]))

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
  (define curr (get-node-by-index index tree)) ; I could just pass curr in...
  ;; generate the children
  (define children
    (cull-bad-nodes ;; this gets rid of the useless nodes created down below
     (map
      (lambda ([ax : axiom]) : node
        (match (ax (node-data curr))
          [(? list? st) (node (fresh-index) (cast st stmt) index '())]
          [_ (node -1 '() -1 '())])) ;; this case occurs if the axiom could not be applied
      axioms)))
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
      children)))
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
     (list (node (fresh-index) hypothesis -1 '())))))
  (void))

(provide (all-defined-out))
