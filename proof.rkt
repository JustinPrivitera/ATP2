#lang typed/racket

(require typed/rackunit)

;; we will deal purely with natural numbers
(define-type parity (U 'even 'odd 'unknown-parity))
(define-type expr (U binop Natural Symbol 'unknown-value))
(struct binop ([op : Symbol] [left : expr] [right : expr])#:transparent)

(struct nat ([name : Symbol] [par : parity] [value : expr])#:transparent)
(define-type stmt (Listof nat)) ; a statement of truth about specific natural numbers

;; nodes for the tree
(struct node
  ([index : Integer]
   [data : stmt]
   [parent : Integer] ;; root has -1 parent
   [children : (Listof Integer)])#:transparent)

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
      (~a name) ": [" (~a par) "] [" (expr-to-string val) "]\n"
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
(define (generate-path [index : Integer] [tree : (Listof node)]) : (Listof  String)
  (define curr (get-node-by-index index tree))
  (define parent (node-parent curr))
  (if (equal? -1 parent)
      (list (stmt-to-string (node-data curr)))
      (append (list (stmt-to-string (node-data curr))) (generate-path parent tree))))

;; non-strict
(define (expr-equals? [e1 : expr] [e2 : expr]) : Boolean
  (match* (e1 e2)
    [((binop sym1 a b) (binop sym2 c d))
     (and (equal? sym1 sym2) (expr-equals? a c) (expr-equals? b d))]
    [((? natural? n1) (? natural? n2))
     (equal? n1 n2)]
    [((? symbol? s1) (? symbol? s2))
     (equal? s1 s2)]
    [('unknown-value _) #t]
    [(_ _) #f]))

;; non-strict
(define (parity-equals? [p1 : parity] [p2 : parity]) : Boolean
  (or (equal? p1 'unknown-parity) (equal? p1 p2)))

;; does not take into account the name
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
     (nat-equals? n (get-nat-by-name (nat-name n) curr))) cncl))

(provide (all-defined-out))
