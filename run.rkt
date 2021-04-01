#lang typed/racket

(require "proof.rkt")

;; axioms

;; axiom 1 helper
(define (even-forward-helper
         [st : stmt]
         [var-name : Symbol]
         [done-already? : Boolean]) : (Listof Any)
  (define done? (box done-already?))
  (match st
    [(cons first rest)
     (cons
      (if
       (and (not done-already?)
            (equal? (nat-par first) 'even)
            (equal? (nat-value first) 'unknown-value))
       (begin
         (set-box! done? #t)
         (list
          (nat (nat-name first) (nat-par first) (binop '* 2 var-name))
          (nat var-name 'unknown-parity 'unknown-value)))
       first)
      (even-forward-helper rest var-name (unbox done?)))]
    ['() '()]))

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [st : stmt]) : (U stmt Void)
  (if ;; if the axiom is applicable
   (match st
     ['() #f]
     [_ (ormap
         (lambda ([n : nat]) : Boolean
           (and (equal? (nat-par n) 'even) (equal? (nat-value n) 'unknown-value)))
         st)])
   (cast (flatten (even-forward-helper st (string->symbol (~a (fresh-char))) #f)) stmt)
   (void)))

;; axiom 2 helper
(define (even-reverse-helper
         [st : stmt]
         [var-name : Symbol]
         [done-already? : Boolean]) : (Listof nat)
  (define done? (box done-already?))
  (match st
    [(cons first rest)
     (cons
      (if
       (and (not done-already?)
            (expr-equals? (parse '(* 2 _)) (nat-value first))
            (equal? (nat-par first) 'unknown-parity))
       (begin
         (set-box! done? #t)
         (nat (nat-name first) 'even (nat-value first)))
       first)
      (even-reverse-helper rest var-name (unbox done?)))]
    ['() '()]))

;; axiom 2: if a = 2b for some b, then a is even
(define (even-reverse [st : stmt]) : (U stmt Void)
  (if ;; if the axiom is applicable
   (match st
     ['() #f]
     [_ (ormap
         (lambda ([n : nat]) : Boolean
           (and
            (expr-equals? (parse '(* 2 _)) (nat-value n))
            (equal? (nat-par n) 'unknown-parity)))
         st)])
   (even-reverse-helper st (string->symbol (~a (fresh-char))) #f)
   (void)))

(define (subst-helper
         [st : stmt]
         [var-name : Symbol]
         [done-already? : Boolean]) : (Listof nat)
  (define done? (box done-already?))
  (match st
    [(cons first rest)
     (cons
      (if
       (and (not done-already?)
            (expr-equals? (parse '(* 2 _)) (nat-value first))
            (equal? (nat-par first) 'unknown-parity))
       (begin
         (set-box! done? #t)
         (nat (nat-name first) 'even (nat-value first)))
       first)
      (even-reverse-helper rest var-name (unbox done?)))]
    ['() '()]))

;; axiom 3: substitution
(define (subst [st : stmt]) : (U stmt Void)
  (if ;; if the axiom is applicable
   (match st
     ['() #f]
     [_ (define var-names (get-names-from-stmt st))
        (ormap
         (lambda ([n : nat]) : Boolean
           (and
            (expr-equals? (parse '(* 2 _)) (nat-value n))
            (equal? (nat-par n) 'unknown-parity)))
         st)])
   (even-reverse-helper st (string->symbol (~a (fresh-char))) #f)
   (void)))

(define axioms (list even-forward even-reverse))

;; proof 1
(define hypo (box (list (nat 'x 'even 'unknown-value))))
(define cncl (box (list (nat 'x 'even (parse '(* 2 a))))))
(display "Given x even, prove that x = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)

;; proof 2
(set-box! hypo (list (nat 'x 'even 'unknown-value)
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even (parse '(* 2 a)))
                     (nat 'y 'even (parse '(* 2 b)))))
(display "\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
(prove (unbox hypo) (unbox cncl) axioms)

;; proof 3
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nGiven x = (* 2 y) for some y, prove that x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)

;; proof 4
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)
                     (nat 'z 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)
                     (nat 'z 'even (parse '(* 2 _)))))
(display "\nGiven x = (* 2 y) for some y and z even, prove that x is even and z = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)
