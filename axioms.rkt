#lang typed/racket

(require racket/set)
(require "definitions.rkt")
(require "proof.rkt")
(require "lookup.rkt")
(require "equality.rkt")

;; make an axiom builder function to cut down on code
;; is it possible to pass a match pattern to a function???

;; axioms

;; still need:
;;;; comm (+ a b) -> (+ b a)
;;;; assoc (+ a (+ b c)) <-> (+ (+ a b) c)
;;;; simp (+ [n1] [n2]) -> [n1 + n2]
;; the above three can prove the sum of two odds is even and sum of even odd is odd

;;;; factor integers? if trying to pull out a common factor see if the integer is divisible

;; need tests for other axioms

;; idea: each time an axiom is run, double the info list
;; so take each stmt and reverse it and add to the list
;; then we only search through the list once instead of checking rhs and lhs
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

(define (construct-arith-axiom
         [mark-sub-exprs : (-> expand expand)]
         [replace-once : (-> expand Integer expand)]
         [facts : info]) : (Listof info)
  (: new-stmts (Boxof (Listof info)))
  (: potential-exprs (Boxof (Listof expr)))
  (: my-expand (Boxof expand))
  (define new-stmts (box '()))
  (define potential-exprs (box '()))
  (define my-expand (box (expand 0 NO-INDEX)))
  (begin
    (map
     (lambda ([st : stmt]) : Void
       (match (stmt-lhs st)
         [(? parity? _) (void)]
         [(? expr? e)
          (set-box! potential-exprs
                    (begin
                      (set-box! my-expand (mark-sub-exprs (expanded-form e)))
                      (map
                       regular-form
                       (map
                        (lambda ([ind : Integer]) : expand
                          (replace-once (unbox my-expand) ind))
                        (range (increment-and-reset-se-index))))))
          (map
           (lambda ([potential-e : expr]) : Void
             (if (not (info-equals?
                       (list (stmt (stmt-rhs st) potential-e))
                       (get-stmt-from-info (stmt-rhs st) facts) STRICT))
                 (set-box!
                  new-stmts
                  (cons
                   (list (stmt potential-e (stmt-rhs st)))
                   (unbox new-stmts)))
                 (void)))
           (unbox potential-exprs))
          (void)]))
     (double-info facts)))
  (map
   (lambda ([new-stmt : info]) : info
     (append facts new-stmt))
   (unbox new-stmts)))

;; axiom 4: factorization
(define (factor [facts : info]) : (Listof info)
  (: mark-sub-exprs (-> expand expand))
  (define mark-sub-exprs
    (lambda ([ex : expand]) : expand
     (match ex
       [(expand (binop-ex
                 '+
                 (expand (binop-ex '* a b) ind-l)
                 (expand (binop-ex '* c d) ind-r))
                ind-p)
        (expand (binop-ex
                 '+
                 (mark-sub-exprs (expand (binop-ex '* a b) ind-l))
                 (mark-sub-exprs (expand (binop-ex '* c d) ind-r)))
                (if (expr-equals-strict? (regular-form a) (regular-form c))
                    (fresh-se-index)
                    ind-p))]
       [(expand (binop-ex
                 '+
                 (expand (binop-ex '* a b) ind-l)
                 c)
                ind-p)
        (expand (binop-ex
                 '+
                 (mark-sub-exprs (expand (binop-ex '* a b) ind-l))
                 (mark-sub-exprs c))
                (if (expr-equals-strict? (regular-form a) (regular-form c))
                    (fresh-se-index)
                    ind-p))]
       [(expand (binop-ex sym left right) ind)
        (expand (binop-ex sym (mark-sub-exprs left) (mark-sub-exprs right)) ind)]
       [_ ex])))
  (: factor-once (-> expand Integer expand))
  (define factor-once
    (lambda ([ex : expand] [index : Integer]) : expand
      (match ex
        [(expand (binop-ex
                  '+
                  (expand (binop-ex '* a b) ind-l)
                  (expand (binop-ex '* c d) ind-r))
                 ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand (binop-ex '* a (expand (binop-ex '+ b d) ind-r)) ind-p)
             (expand (binop-ex
                      '+
                      (factor-once (expand (binop-ex '* a b) ind-l) index)
                      (factor-once (expand (binop-ex '* c d) ind-r) index))
                     ind-p))]
        [(expand (binop-ex
                  '+
                  (expand (binop-ex '* a b) ind-l)
                  c)
                 ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand (binop-ex '* a (expand (binop-ex '+ b (expand 1 NO-INDEX)) ind-l)) ind-p)
             (expand (binop-ex
                      '+
                      (factor-once (expand (binop-ex '* a b) ind-l) index)
                      (factor-once c index))
                     ind-p))]
        [(expand (binop-ex sym left right) ind)
         (expand (binop-ex sym (factor-once left index) (factor-once right index)) ind)]
        [_ ex])))
  (construct-arith-axiom
   mark-sub-exprs
   factor-once
   facts))

;; commutativity
(define (comm [facts : info]) : (Listof info)
  ;; essentially, annotate the expression tree, giving each sub expression
  ;; for which the axiom is applicable a unique identifier to be used later
  (: mark-sub-exprs (-> expand expand))
  (define mark-sub-exprs ; mark the matching sub-expressions - remember to reset se-index after use!
    (lambda ([ex : expand]) : expand
      (match ex
        [(expand (binop-ex sym a b) _) ; mark any binop
         (expand (binop-ex sym (mark-sub-exprs a) (mark-sub-exprs b)) (fresh-se-index))]
        [_ ex])))
  (: exec-once (-> expand Integer expand))
  (define exec-once ; mark the matching sub-expressions - remember to reset se-index after use!
    (lambda ([ex : expand] [index : Integer]) : expand
      (match ex
        [(expand (binop-ex sym a b) ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand (binop-ex sym b a) ind-p)
             (expand (binop-ex sym (exec-once a index) (exec-once b index)) ind-p))]
        [_ ex])))
  (construct-arith-axiom
   mark-sub-exprs
   exec-once
   facts))

;; simplification
(define (simp [facts : info]) : (Listof info)
  ;; essentially, annotate the expression tree, giving each sub expression
  ;; for which the axiom is applicable a unique identifier to be used later
  (: mark-sub-exprs (-> expand expand))
  (define mark-sub-exprs ; mark the matching sub-expressions - remember to reset se-index after use!
    (lambda ([ex : expand]) : expand
      (match ex
        [(expand (binop-ex sym (expand (? integer? a) ind-l) (expand (? integer? b) ind-r)) _) ; mark
         (expand (binop-ex sym (expand a ind-l) (expand b ind-r)) (fresh-se-index))]
        [(expand (binop-ex sym a b) ind) ; mark any binop
         (expand (binop-ex sym (mark-sub-exprs a) (mark-sub-exprs b)) ind)]
        [_ ex])))
  (: exec-once (-> expand Integer expand))
  (define exec-once ; mark the matching sub-expressions - remember to reset se-index after use!
    (lambda ([ex : expand] [index : Integer]) : expand
      (match ex
        [(expand (binop-ex sym (expand (? integer? a) ind-l) (expand (? integer? b) ind-r)) ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand ((symbol->op sym) a b) ind-p)
             (expand (binop-ex sym (expand a ind-l) (expand b ind-r)) ind-p))]
        [(expand (binop-ex sym a b) ind-p)
         (expand (binop-ex sym (exec-once a index) (exec-once b index)) ind-p)]
        [_ ex])))
  (construct-arith-axiom
   mark-sub-exprs
   exec-once
   facts))

;; associativity
(define (assoc [facts : info]) : (Listof info)
  (: mark-sub-exprs (-> expand expand))
  (define mark-sub-exprs
    (lambda ([ex : expand]) : expand
     (match ex
       [(expand (binop-ex
                 sym1
                 a
                 (expand (binop-ex sym2 b c) ind-r))
                ind-p)
        (expand (binop-ex
                 sym1
                 (mark-sub-exprs a)
                 (mark-sub-exprs (expand (binop-ex sym2 b c) ind-r)))
                (if (equal? sym1 sym2)
                    (fresh-se-index)
                    ind-p))]
       [(expand (binop-ex
                 sym1
                 (expand (binop-ex sym2 a b) ind-r)
                 c)
                ind-p)
        (expand (binop-ex
                 sym1
                 (mark-sub-exprs (expand (binop-ex sym2 a b) ind-r))
                 (mark-sub-exprs c))
                (if (equal? sym1 sym2)
                    (fresh-se-index)
                    ind-p))]
       [(expand (binop-ex sym left right) ind)
        (expand (binop-ex sym (mark-sub-exprs left) (mark-sub-exprs right)) ind)]
       [_ ex])))
  (: exec-once (-> expand Integer expand))
  (define exec-once
    (lambda ([ex : expand] [index : Integer]) : expand
      (match ex
        [(expand (binop-ex
                  sym1
                  a
                  (expand (binop-ex sym2 b c) ind-r))
                 ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand (binop-ex sym1 (expand (binop-ex sym2 a b) ind-r) c) ind-p)
             (expand (binop-ex
                      sym1
                      (exec-once a index)
                      (exec-once (expand (binop-ex sym2 b c) ind-r) index))
                     ind-p))]
        [(expand (binop-ex
                  sym1
                  (expand (binop-ex sym2 a b) ind-l)
                  c)
                 ind-p)
         (if (equal? ind-p index) ; perform the change
             (expand (binop-ex
                      sym1
                      a
                      (expand (binop-ex sym2 b c) ind-l))
                     ind-p)
             (expand (binop-ex
                      sym1
                      (exec-once (expand (binop-ex sym2 a b) ind-l) index)
                      (exec-once c index))
                     ind-p))]
        [(expand (binop-ex sym left right) ind)
         (expand (binop-ex sym (exec-once left index) (exec-once right index)) ind)]
        [_ ex])))
  (construct-arith-axiom
   mark-sub-exprs
   exec-once
   facts))

(define axioms
  (list
   (cons even-forward "even-forward")
   (cons even-reverse "even-reverse")
   (cons odd-forward "odd-forward")
   (cons odd-reverse "odd-reverse")
   (cons subst "subst")
   (cons factor "factor")
   (cons comm "comm")
   (cons assoc "assoc")
   (cons simp "simp")))

(define ch34ts
  (list
   (cons even-forward "even-forward")
   (cons even-reverse "even-reverse")
   (cons odd-forward "odd-forward")
   (cons odd-reverse "odd-reverse")
   #;(cons subst "subst")))

(provide (all-defined-out))
