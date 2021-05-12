#lang typed/racket

(require "definitions.rkt")

(define (get-stmt-from-info [val : attr] [facts : info]) : info
  (match facts
    [(cons (stmt lhs rhs) rest)
     (cond
       [(equal? lhs val) (cons (stmt lhs rhs) (get-stmt-from-info val rest))]
       [(equal? rhs val) (cons (stmt lhs rhs) (get-stmt-from-info val rest))]
       [else (get-stmt-from-info val rest)])]
    ['() '()]))

(define (get-node-by-index [index : Integer] [nodes : (Listof node)]) : node
  (match nodes
    [(cons first rest)
     (if (equal? index (node-index first))
         first
         (get-node-by-index index rest))]
    ['() (error 'get-node-by-index "node with index '~a' not found" index)]))

;; get all the nodes in the tree except the node with the specified index
(define (get-all-from-except [tree : (Listof node)] [index : Integer]) : (Listof node)
  (match tree
    [(cons first rest)
     (if (equal? (node-index first) index)
         (get-all-from-except rest index)
         (append (list first) (get-all-from-except rest index)))]
    ['() '()]))

(define (get-expr-expr-pairs [facts : info]) : info
  (match facts
    [(cons (stmt (? parity? p) _) rest) (get-expr-expr-pairs rest)]
    [(cons (stmt _ (? parity? p)) rest) (get-expr-expr-pairs rest)]
    [(cons first rest) (cons first (get-expr-expr-pairs rest))]
    ['() '()]))

(define (symbol->op [sym : Symbol]) : (-> Integer Integer Integer)
  (match sym
    ['+ +]
    ['* *]))

(provide (all-defined-out))
