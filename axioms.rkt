#lang typed/racket

(require racket/set)
(require "definitions.rkt")
(require "proof.rkt")
(require "lookup.rkt")
(require "equality.rkt")

;; idea: each time an axiom is run, double the info list
;; so take each stmt and reverse it and add to the list
;; then we only search through the list once instead of checking rhs and lhs

;; axioms

;; still need:
;;;; comm (+ a b) -> (+ b a)
;;;; assoc (+ a (+ b c)) <-> (+ (+ a b) c)
;;;; simp (+ [n1] [n2]) -> [n1 + n2]
;; the above three can prove the sum of two odds is even and sum of even odd is odd

;;;; factor integers? if trying to pull out a common factor see if the integer is divisible

;; need tests for other axioms

(define (double-info [facts : info]) : info
  (match facts
    [(cons (stmt left right) rest)
     (cons (stmt left right)
           (cons (stmt right left)
                 (double-info rest)))]
    ['() '()]))

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [facts : info]) : (Listof info)
  (: var-names (Boxof (Listof Symbol)))
  (: new-stmts (Boxof (Listof info)))
  (define var-names (box '()))
  (define new-stmts (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt 'even rhs)
          (if (not (info-equals?
                    (list (stmt rhs (parse '(* 2 '_))))
                    (get-stmt-from-info rhs facts) NOT-STRICT))
           (begin
             (set-box! var-names
                       (cons
                        (string->symbol (~a (fresh-char)))
                        (unbox var-names)))
             (set-box! new-stmts
                       (cons
                        (list (stmt (binop '* 2 (first (unbox var-names))) rhs))
                        (unbox new-stmts))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (map
     (lambda ([new-stmt : info]) : info
       (append facts new-stmt))
     (unbox new-stmts))))

;; axiom 2: if a = 2b for some b, then a is even
(define (even-reverse [facts : info]) : (Listof info)
  (: new-stmts (Boxof (Listof info)))
  (define new-stmts (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt (binop '* 2 _) rhs)
          (if
           (and (not (equal? rhs 'even))
                (not (info-equals?
                      (list (stmt rhs 'even))
                      (get-stmt-from-info rhs facts) NOT-STRICT)))
           (set-box! new-stmts
                     (cons
                      (list (stmt 'even rhs))
                      (unbox new-stmts)))
           (void))]
         [_ (void)]))
     (double-info facts))
    (map
     (lambda ([new-stmt : info]) : info
       (append facts new-stmt))
     (unbox new-stmts))))

;; axiom 1: if a is odd, then a = 2b + 1 for some b
(define (odd-forward [facts : info]) : (Listof info)
  (: var-names (Boxof (Listof Symbol)))
  (: new-stmts (Boxof (Listof info)))
  (define var-names (box '()))
  (define new-stmts (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt 'odd rhs)
          (if (not (info-equals?
                    (list (stmt rhs (parse '(+ (* 2 '_) 1))))
                    (get-stmt-from-info rhs facts) NOT-STRICT))
           (begin
             (set-box! var-names
                       (cons
                        (string->symbol (~a (fresh-char)))
                        (unbox var-names)))
             (set-box! new-stmts
                       (cons
                        (list (stmt (binop '+ (binop '* 2 (first (unbox var-names))) 1) rhs))
                        (unbox new-stmts))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (map
     (lambda ([new-stmt : info]) : info
       (append facts new-stmt))
     (unbox new-stmts))))

;; if a = 2b + 1 for some b, then a is odd
(define (odd-reverse [facts : info]) : (Listof info)
  (: new-stmts (Boxof (Listof info)))
  (define new-stmts (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt (binop '+ (binop '* 2 _) 1) rhs)
          (if
           (and (not (equal? rhs 'odd))
                (not (info-equals?
                      (list (stmt rhs 'odd))
                      (get-stmt-from-info rhs facts) NOT-STRICT)))
           (set-box! new-stmts
                     (cons
                      (list (stmt 'odd rhs))
                      (unbox new-stmts)))
           (void))]
         [_ (void)]))
     (double-info facts))
    (map
     (lambda ([new-stmt : info]) : info
       (append facts new-stmt))
     (unbox new-stmts))))

;; axiom 3: substitution
(define (subst [facts : info]) : (Listof info)
  (: new-stmts (Boxof (Listof info)))
  (define new-stmts (box '()))
  (define ex-ex-pairs (double-info (get-expr-expr-pairs facts)))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match (stmt-lhs st)
         [(? parity? _) (void)]
         [(? expr? e)
          (map
           (lambda ([e-e-pair : stmt]) : Void
             (match e-e-pair
               [(stmt left-expr right-expr)
                (if (and
                     (expr-in-expr left-expr e)
                     (not (info-equals?
                           (list
                            (stmt
                             (subst-expr right-expr left-expr e)
                             (stmt-rhs st)))
                           (get-stmt-from-info (stmt-rhs st) facts) #f)))
                    (set-box! new-stmts
                              (cons
                               (list
                                (stmt
                                 (subst-expr right-expr left-expr e)
                                 (stmt-rhs st)))
                               (unbox new-stmts)))
                    (void))]))
           (set->list
            (set-subtract
             (list->set ex-ex-pairs)
             (list->set (list st (stmt (stmt-rhs st) (stmt-lhs st)))))))
          (void)]))
     (double-info facts)))
  (map
   (lambda ([new-stmt : info]) : info
     (append facts new-stmt))
   (unbox new-stmts)))

;; axiom 4: factorization
(define (factor [facts : info]) : (Listof info)
  (: helper (-> expr expr))
  (define helper
    (lambda ([ex : expr]) : expr
      (match ex
        [(binop '+ (binop '* a b) (binop '* c d))
         (if (expr-equals-strict? a c)
             (binop '* a (binop '+ b d))
             ex)]
        [(binop '+ (binop '* a b) c)
         (if (expr-equals-strict? a c)
             (binop '* a (binop '+ b 1))
             ex)]
        [(binop sym left right)
         (binop sym (helper left) (helper right))]
                  [_ ex])))
  (: new-stmts (Boxof (Listof info)))
  (: potential-expr (Boxof expr))
  (define new-stmts (box '()))
  (define potential-expr (box '_))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match (stmt-lhs st)
         [(? parity? _) (void)]
         [(? expr? e)
          (set-box! potential-expr (helper e))
          (if (not (info-equals?
                    (list (stmt (stmt-rhs st) (unbox potential-expr)))
                    (get-stmt-from-info (stmt-rhs st) facts) #f))
              (set-box!
               new-stmts
               (cons
                (list (stmt (unbox potential-expr) (stmt-rhs st)))
                (unbox new-stmts)))
                  (void))]))
     (double-info facts)))
  (map
   (lambda ([new-stmt : info]) : info
     (append facts new-stmt))
   (unbox new-stmts)))

(define axioms
  (list
   (cons even-forward "even-forward")
   (cons even-reverse "even-reverse")
   ;(cons odd-forward "odd-forward")
   ;(cons odd-reverse "odd-reverse")
   (cons subst "subst")
   (cons factor "factor")))

(provide (all-defined-out))
