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

;; rearrangement axiom: (* a 2) <--> (* 2 a)
;; tell me what axiom was used each step of the way
;; if x = y then y = x
;; solve: if n1, n2 are constants and n1 + n2 = n3, then (+ n1 n2) = n3
;; odd forward and odd reverse
;; reverse subst
;; instead of each axiom taking first opportunity to act, should be applied the number
;; of times that it can act, and on each different thing it can act on

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
  (: done? (Boxof Boolean))
  (: var-name (Boxof Symbol))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define var-name (box '_))
  (define new-stmt (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt 'even rhs)
          (if
           (and (not (unbox done?))
                (not (info-equals?
                      (list (stmt rhs (parse '(* 2 '_))))
                      (get-stmt-from-info rhs facts) #f)))
           (begin
             (set-box! done? #t)
             (set-box! var-name (string->symbol (~a (fresh-char))))
             (set-box! new-stmt (list (stmt (binop '* 2 (unbox var-name)) rhs))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (list (append facts (unbox new-stmt)))))
#|
;; axiom 2: if a = 2b for some b, then a is even
(define (even-reverse [facts : info]) : info
  (: done? (Boxof Boolean))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define new-stmt (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt (binop '* 2 _) rhs)
          (if
           (and (not (unbox done?))
                (not (equal? rhs 'even))
                (not (info-equals?
                      (list (stmt rhs 'even))
                      (get-stmt-from-info rhs facts) #f)))
           (begin
             (set-box! done? #t)
             (set-box! new-stmt (list (stmt 'even rhs))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (append facts (unbox new-stmt))))

;; axiom 1: if a is even, then a = 2b for some b
(define (odd-forward [facts : info]) : info
  (: done? (Boxof Boolean))
  (: var-name (Boxof Symbol))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define var-name (box '_))
  (define new-stmt (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt 'odd rhs)
          (if
           (and (not (unbox done?))
                (not (info-equals?
                      (list (stmt rhs (parse '(+ (* 2 '_) 1))))
                      (get-stmt-from-info rhs facts) #f)))
           (begin
             (set-box! done? #t)
             (set-box! var-name (string->symbol (~a (fresh-char))))
             (set-box! new-stmt (list (stmt (binop '+ (binop '* 2 (unbox var-name)) 1) rhs))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (append facts (unbox new-stmt))))

;; axiom 2: if a = 2b for some b, then a is even
(define (odd-reverse [facts : info]) : info
  (: done? (Boxof Boolean))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define new-stmt (box '()))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match st
         [(stmt (binop '+ (binop '* 2 _) 1) rhs)
          (if
           (and (not (unbox done?))
                (not (equal? rhs 'odd))
                (not (info-equals?
                      (list (stmt rhs 'odd))
                      (get-stmt-from-info rhs facts) #f)))
           (begin
             (set-box! done? #t)
             (set-box! new-stmt (list (stmt 'odd rhs))))
           (void))]
         [_ (void)]))
     (double-info facts))
    (append facts (unbox new-stmt))))

;; axiom 3: substitution
(define (subst [facts : info]) : info
  (: done? (Boxof Boolean))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define new-stmt (box '()))
  (define ex-ex-pairs (double-info (get-expr-expr-pairs facts)))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (if (unbox done?)
           (void)
           (match (stmt-lhs st)
             [(? parity? _) (void)]
             [(? expr? e)
              (map
               (lambda ([e-e-pair : stmt]) : Void
                 (if (unbox done?)
                     (void)
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
                            (begin
                              (set-box! done? #t)
                              (set-box! new-stmt
                                        (list
                                         (stmt
                                          (subst-expr right-expr left-expr e)
                                          (stmt-rhs st)))))
                            (void))])))
               (set->list
                (set-subtract
                 (list->set ex-ex-pairs)
                 (list->set (list st (stmt (stmt-rhs st) (stmt-lhs st)))))))
              (void)])))
     (double-info facts)))
  (append facts (unbox new-stmt)))

;; axiom 4: factorization
(define (factor [facts : info]) : info
  (: helper (-> expr (Boxof Boolean) expr))
  (define helper
    (lambda ([ex : expr] [done? : (Boxof Boolean)]) : expr
            (if (unbox done?)
                ex
                (match ex
                  [(binop '+ (binop '* a b) (binop '* c d))
                   (if (expr-equals-strict? a c)
                       (begin
                         (set-box! done? #t)
                         (binop '* a (binop '+ b d)))
                       ex)]
                  [(binop sym left right)
                   (binop sym (helper left done?) (helper right done?))]
                  [_ ex]))))
  (: done? (Boxof Boolean))
  (: new-stmt (Boxof info))
  (: potential-expr (Boxof expr))
  (define done? (box #f))
  (define new-stmt (box '()))
  (define potential-expr (box '_))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (if (unbox done?)
           (void)
           (match (stmt-lhs st)
             [(? parity? _) (void)]
             [(? expr? e)
              (set-box! potential-expr (helper e done?))
              (if (and
                   (unbox done?)
                   (not (info-equals?
                         (list (stmt (stmt-rhs st) (unbox potential-expr)))
                         (get-stmt-from-info (stmt-rhs st) facts) #f)))
                  (set-box!
                   new-stmt
                   (list (stmt (unbox potential-expr) (stmt-rhs st))))
                  (void))])))
     (double-info facts)))
  (append facts (unbox new-stmt)))
|#

(define axioms
  (list
   (cons even-forward "even-forward")
   #;(cons even-reverse "even-reverse")
   ;(cons odd-forward "odd-forward")
   ;(cons odd-reverse "odd-reverse")
   #;(cons subst "subst")
   #;(cons factor "factor")))

(provide (all-defined-out))
