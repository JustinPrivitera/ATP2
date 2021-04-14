#lang typed/racket

(require "definitions.rkt")

#;(define (get-nat-by-name [name : Symbol] [curr : (Listof nat)]) : nat
  (match curr
    [(cons (nat curr-name par val) rest)
     (if (equal? name curr-name)
         (nat curr-name par val)
         (get-nat-by-name name rest))]
    ['() (error 'get-nat-by-name "name not found: '~a'" name)]))

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

#;(define (get-names-from-stmt [st : (Listof nat)]) : (Listof Symbol)
  (match st
    [(cons (nat name _ _) rest) (cons name (get-names-from-stmt rest))]
    ['() '()]))

(provide (all-defined-out))
