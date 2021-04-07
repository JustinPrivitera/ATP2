#lang typed/racket

(require "proof.rkt")

;; axioms

;; rearrangement axiom: (* a 2) <--> (* 2 a)
;; tell me what axiom was used each step of the way

;; axiom 1: if a is even, then a = 2b for some b
(define (even-forward [st : stmt]) : stmt
  (: done? (Boxof Boolean))
  (define done? (box #f))
  (define var-name (string->symbol (~a (fresh-char))))
  (cast
   (flatten
    (map
     (lambda ([n : nat]) : (Listof nat)
       (if
        (and (not (unbox done?))
             (equal? (nat-par n) 'even)
             (equal? (nat-value n) 'unknown-value))
        (begin
          (set-box! done? #t)
          (list
           (nat (nat-name n) (nat-par n) (binop '* 2 var-name))
           (nat var-name 'unknown-parity 'unknown-value)))
        (list n)))
     st))
   stmt))

;; axiom 2: if a = 2b for some b, then a is even
(define (even-reverse [st : stmt]) : stmt
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
(define (subst [st : stmt]) : stmt
  (: done? (Boxof Boolean))
  (define done? (box #f))
  (define who (box '_)) ;; who is being substituted
  (map
   (lambda ([n : nat]) : nat
     (if (unbox done?)
         n
         (match
             (match
                 (filter
                  (lambda ([v : Symbol]) : Boolean
                    (var-in-expr v (nat-value n)))
                  (get-names-from-stmt st))
               ['() '_]
               [(? list? l) (first l)])
           ['_ n]
           [who ;; who is being substituted
            (set-box! done? #t)
            (nat
             (nat-name n)
             (nat-par n)
             (subst-var
              who
              (nat-value (get-nat-by-name who st))
              (nat-value (get-nat-by-name (nat-name n) st))))])))
   st))

;; axiom 4: factorization
(define (factor [st : stmt]) : stmt
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

(define axioms (list even-forward even-reverse subst factor))

;; proof 1
(define hypo (box (list (nat 'x 'even 'unknown-value))))
(define cncl (box (list (nat 'x 'even (parse '(* 2 a))))))
(display "Proof 1:\nGiven x even, prove that x = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 2
(set-box! hypo (list (nat 'x 'even 'unknown-value)
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even (parse '(* 2 a)))
                     (nat 'y 'even (parse '(* 2 b)))))
(display "\nProof 2:\nGiven x even, y even, prove that x = (* 2 a) and y = (* 2 b) for some a and b.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 3
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 3:\nGiven x = (* 2 y) for some y, prove that x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 4
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(* 2 y)))
                     (nat 'y 'unknown-parity 'unknown-value)
                     (nat 'z 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)
                     (nat 'z 'even (parse '(* 2 _)))))
(display "\nProof 4:\nGiven x = (* 2 y) for some y and z even, prove that x is even and z = (* 2 a) for some a.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 5
(set-box! hypo (list (nat 'x 'unknown-parity (parse 'y))
                     (nat 'y 'unknown-parity (parse '(* 2 z)))
                     (nat 'z 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 5:\nGiven x = y and y = (* 2 z) for some z, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 6
(set-box! hypo (list (nat 'x 'unknown-parity (parse 'y))
                     (nat 'y 'even 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 6:\nGiven x = y and y is even, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")

;; proof 7
(set-box! hypo (list (nat 'x 'unknown-parity (parse '(+ (* 2 a) (* 2 b))))
                     (nat 'a 'unknown-parity 'unknown-value)
                     (nat 'a 'unknown-parity 'unknown-value)))
(set-box! cncl (list (nat 'x 'even '_)))
(display "\nProof 7:\nGiven x = (+ (* 2 a) (* 2 b)) for some a and b, prove x is even.\n")
(prove (unbox hypo) (unbox cncl) axioms)
(display "================================\n")
