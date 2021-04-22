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

;; need tests for other axioms

(define (double-info [facts : info]) : info
  (match facts
    [(cons (stmt left right) rest)
     (cons (stmt left right)
           (cons (stmt right left)
                 (double-info rest)))]
    ['() '()]))

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [facts : info]) : info
  (: done? (Boxof Boolean))
  (: var-name (Boxof Symbol))
  (: new-stmt (Boxof info))
  (define done? (box #f))
  (define var-name (box '_))
  (define alt-facts (double-info facts))
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
                      (get-stmt-from-info rhs alt-facts) #f)))
           (begin
             (set-box! done? #t)
             (set-box! var-name (string->symbol (~a (fresh-char))))
             (set-box! new-stmt (list (stmt (binop '* 2 (unbox var-name)) rhs))))
           (void))]
         [_ (void)]))
     alt-facts)
    (append facts (unbox new-stmt))))

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
                        (if (expr-in-expr left-expr e)
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

#;(define (subst [st : (Listof nat)]) : (Listof nat)
  (: done? (Boxof Boolean))
  (define done? (box #f))
  (: what (Boxof expr))
  (define what (box 0))
  (map
   (lambda ([n : nat]) : nat
     (if (unbox done?)
         n
         (match
             (match
                 (filter
                  (lambda ([v : Symbol]) : Boolean
                    (if (var-in-expr v (nat-value n))
                        (begin
                          (set-box! what (nat-value (get-nat-by-name v st)))
                          (not (equal? 'unknown-value (unbox what))))
                        #f))
                  (get-names-from-stmt st))
               ['() '_]
               [(? list? l) (first l)])
           ['_ n]
           [who ;; who is being substituted
            (set-box! what (nat-value (get-nat-by-name who st)))
            (if (equal? (unbox what) 'unknown-value)
                n
                (begin
                  (set-box! done? #t)
                  (nat
                   (nat-name n)
                   (nat-par n)
                   (subst-var
                    who
                    (unbox what)
                    (nat-value n)))))])))
   st))

;; axiom 4: factorization
#;(define (factor [st : (Listof nat)]) : (Listof nat)
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
  (define done? (box #f))
  (map
   (lambda ([n : nat]) : nat
     (if (unbox done?)
         n
         (nat
          (nat-name n)
          (nat-par n)
          (helper (nat-value n) done?))))
   st))

(define axioms
  (list
   (cons even-forward "even-forward")
   (cons even-reverse "even-reverse")
   (cons subst "subst")
   #;(cons factor "factor")))

(provide (all-defined-out))
