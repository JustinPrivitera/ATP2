#lang typed/racket

(require "definitions.rkt")
(require "proof.rkt")
(require "lookup.rkt")
(require "equality.rkt")

;; axioms

;; rearrangement axiom: (* a 2) <--> (* 2 a)
;; tell me what axiom was used each step of the way
;; if x = y then y = x
;; solve: if n1, n2 are constants and n1 + n2 = n3, then (+ n1 n2) = n3
;; odd forward and odd reverse
;; reverse subst

;; need tests for other axioms

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [facts : info]) : info
  (: done? (Boxof Boolean))
  (: side (Boxof (U 'left 'right 'neither)))
  (: var-name (Boxof Symbol))
  (define done? (box #f))
  (define side (box 'neither))
  (define var-name (box '_))
  (cast
   (flatten
    (map
     (lambda ([st : stmt]) : (Listof stmt)
       (match st
         [(stmt lhs rhs)
          (if
           (and (not (unbox done?))
                (match* (lhs rhs)
                  [('even _) (begin (set-box! side 'left) #t)]
                  [(_ 'even) (begin (set-box! side 'right) #t)]
                     [(_ _) #f]))
           (begin
             (set-box! done? #t)
             (set-box! var-name (string->symbol (~a (fresh-char))))
             (list
              st
              (match (unbox side) ;; which side is 'even
                ['left (stmt (binop '* 2 (unbox var-name)) rhs)]
                ['right (stmt lhs (binop '* 2 (unbox var-name)))])))
           (list st))]))
     facts))
   info))

;; axiom 2: if a = 2b for some b, then a is even
#;(define (even-reverse [st : (Listof nat)]) : (Listof nat)
  (: done? (Boxof Boolean))
  (define done? (box #f))
  (map
   (lambda ([n : nat]) : nat
     (if
      (and (not (unbox done?))
           (expr-equals? (parse '(* 2 _)) (nat-value n))
           (equal? (nat-par n) 'unknown-parity))
      (begin
        (set-box! done? #t)
        (nat (nat-name n) 'even (nat-value n)))
      n))
   st))

;; axiom 3: substitution
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
   #;(cons even-reverse "even-reverse")
   #;(cons subst "subst")
   #;(cons factor "factor")))

(provide (all-defined-out))
