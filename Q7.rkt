#lang racket

(require test-engine/racket-tests)

;; helper methods

(define (reducible? expr)
  (letrec (
           ;; test whether an application, separated by left and right, is reducible.
           [app-reducible?
            (lambda(left right)
              (or 
               (match left
                 [`(λ ,_ ,_) #t]
                 [`(,left ,right) (app-reducible? left right)]
                 [_ #f])
               (match right
                 [`(λ ,_ ,term) (reducible? term)]
                 [`(,left ,right) (app-reducible? left right)]
                 [_ #f])
               ))])
    ;(printf "reducible? ~a\n" expr)
    (match expr
      ;; unlike call-by-value, we need to reduce "things" inside an abstraction
      [`(λ ,var ,term) (reducible? term)]
      [`(,left ,right) (app-reducible? left right)]
      ;; cannot reduce a variable further
      [var #f]
      )
    ))

(define (reduce expr)
  ;(printf "reduce expr:~a\n" expr)
  (match expr
    [`(λ ,var ,term) `(λ ,var ,(reduce term))]
    [`(,t1 ,t2)
     (match (reduce t1)
       [`(λ ,var ,term) (subst var t2 (reduce term))]
       [_ `(,t1 ,(reduce t2))])
     ]
    [var var]
    )
  )

;; Perform alpha-conversion on the expr for a target variable x.
;;
;; This method recurse deeply into each subterm -- it does not 
;; matter if the subterm has another binding for x, because
;; variables are bound by the closest scope.
;;
;; Only "free variables" are left as-is.
(define (a-convert x expr)
  ;(printf "a-convert: x:~a expr:~a\n" x expr)
  (letrec (
           ;; replace all x's in all subterms of expr with y
           [deep-replace 
            (lambda (x y expr)
              (match expr
                [`(λ ,var ,term) 
                 (let ([var-new (if (equal? var x) y var)])
                   `(λ ,var-new ,(deep-replace x y term)))]
                [`(,t1 ,t2) `(,(deep-replace x y t1) ,(deep-replace x y t2))]
                [var (if (equal? var x) y var)]
                ))])
    (let ([fresh (gensym "_v_")]) ;; if this prefix clashes with test cases, I'd be very mad :)
      (deep-replace x fresh expr)
      )))

;; main methods

;; Perform substitution based on page 71's substituion rule
(define (subst x N M)
  ;(printf "subst x:~a N:~a M:~a non-free:~a\n" x N M non-free)
  (match M
    [`(λ ,var ,term)
     ;; alpha convert every abstraction, so that the condition (y not equals x and y not in FV(s)) holds
     (match (a-convert var M)
       [`(λ ,var ,term) `(λ ,var ,(subst x N term))]
       )
     ]
    [`(,t1 ,t2) `(,(subst x N t1) ,(subst x N t2))]
    [var (if (equal? var x) N M)]
    ))

(define (normalize expr)
  ;(printf "normalize expr:~a\n" expr)
  (if (reducible? expr) (normalize (reduce expr)) expr))

;;; test cases
;
;(check-expect (subst 'a 'b 'c) 'c)
;(check-expect (subst 'a 'b 'a) 'b)
;(check-expect (subst 'x 'y '(λ x x)) '(λ 0 0))
;(check-expect (subst 'x 'z '(λ y x)) '(λ 0 z))
;(check-expect (subst 'x 'z '(λ y y)) '(λ 0 0))
;(check-expect (subst 'x 'z '(λ y (λ z x))) '(λ 0 (λ 1 z)))
;
;(check-expect (subst 'x 'z '(((λ y (λ z (λ a a))) (λ y (λ z (λ c z)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ z z))))))
;              '(((λ 0 (λ 1 (λ 2 2))) (λ 0 (λ 1 (λ 2 1)))) ((λ 0 (λ 1 (λ 2 2))) (λ 0 (λ 1 (λ 2 2))))))
;;(subst 'x '(λ jjjj c) '(((λ y (λ z (λ a a))) (λ y (λ z (λ c x)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ x x))))))
;;(subst 'c 'yyyyyy (subst 'x '(λ jjjj c) '(((λ y (λ z (λ a a))) (λ y (λ z (λ c x)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ x x)))))))
;
;(check-expect (normalize '(λ y (λ z x))) '(λ y (λ z x)))
;(check-expect (normalize '((λ y x) (λ x x))) 'x)
;
;;; should be infinite loop in call-by-value, but fine under normal order
;(check-expect (normalize '((λ y x) ((λ x (x x)) (λ x (x x))))) 'x)
;(check-expect (normalize '((λ y (λ y y)) ((λ x (x x)) (λ x (x x))))) '(λ 0 0))
;
;;; reuse Q2's test cases
(check-expect (normalize '(λ x x)) '(λ x x))
(check-expect (normalize '(λ x (x x))) '(λ x (x x)))
(check-expect (normalize '(λ x (x (λ y y)))) '(λ x (x (λ y y))))
(check-expect (normalize '(λ x (λ y y))) '(λ x (λ y y)))
(check-expect (normalize '((λ x x) (λ x (λ b (λ y y))))) '(λ x (λ b (λ y y))))
(check-expect (normalize '((λ x x) ((λ y y) (λ z z)))) '(λ z z))
(check-expect (normalize '((λ y y) (λ z z))) '(λ z z))
(check-expect (normalize '((λ y (y y)) (λ z z))) '(λ z z))
;(check-expect (normalize '((λ x (λ a a)) (λ y y))) '(λ 0 0))
;(check-expect (normalize '((λ x (λ a x)) (λ y y))) '(λ 0 (λ y y)))
(check-expect (normalize '(((λ x x) (λ x x)) (λ x x))) '(λ x x))
;(check-expect (normalize '((λ x (λ a (x x))) (λ y y))) '(λ 0 (λ y y)))
;(check-expect (normalize '((λ x (λ a (x x))) (λ y ((λ z y) (λ z y))))) '(λ 0 (λ y y)))
;(check-expect (normalize '((λ x (λ a (x x))) ((λ z z) (λ b b)))) '(λ 0 (λ b b)))
;(check-expect (normalize '((λ x (λ a (a a))) ((λ z z) (λ b b)))) '(λ 0 (0 0)))
(check-expect (normalize '((λ x x) ((λ x x) (λ z ((λ x x) z))))) '(λ z z))
;(check-expect (normalize '((λ x (λ x (λ x x))) (λ x x))) '(λ 0 (λ 1 1)))
;(check-expect (normalize '((λ x (λ y (λ x x))) (λ z z))) '(λ 0 (λ 1 1)))
;(check-expect (normalize '((λ x (λ x (λ x x))) (λ z z))) '(λ 0 (λ 1 1)))
;(check-expect (normalize '((λ x (λ y (λ x (λ y y)))) (λ z z))) '(λ 0 (λ 1 (λ 2 2))))
;(check-expect (normalize '((λ x (λ y (λ x (λ x x)))) (λ z z))) '(λ 0 (λ 1 (λ 2 2))))
;(check-expect (normalize '((λ x (λ y (λ x (x x)))) (λ z z))) '(λ 0 (λ 1 (1 1))))
;(check-expect (normalize '((λ x (λ y (λ z (x x)))) (λ z z))) '(λ 0 (λ 1 (λ z z))))
;
;;; additional ones
(check-expect (normalize '((λ x (x x)) (λ z z))) '(λ z z))
;(check-expect (normalize '((λ x x) ((λ x x) (λ z ((λ x c) z))))) '(λ z c))
;(check-expect (normalize (normalize (normalize '((λ x (λ z (x x))) (λ z z))))) '(λ 0 (λ z z)))
;(check-expect (normalize '(a b)) '(a b))
;(check-expect (normalize '((λ x (λ z x)) (λ y z))) '(λ 0 (λ y z)))
;(check-expect (normalize '((λ x (λ z (λ y (x y)))) (λ y z))) '(λ 0 (λ 1 z)))
;(check-expect (normalize '((λ x (λ z (λ y (x y)))) (λ y ((z z) (z z))))) '(λ 0 (λ 1 ((z z) (z z)))))
;(check-expect (normalize '((λ x (λ z (λ y (x y)))) (λ y y))) '(λ 0 (λ 1 1)))
;(check-expect (normalize '((λ x (λ z (λ y (y y)))) (λ y y))) '(λ 0 (λ 1 (1 1))))
;(check-expect (normalize '((λ x (λ z (λ y (x x)))) (λ y y))) '(λ 0 (λ 1 (λ y y))))

;(normalize '((λ z (λ x (z z))) (λ y ((x y) z))))
;(normalize '((λ y ((x y) z)) (λ y ((x y) z))))
;(normalize '(λ y ((x y) z)))
(test)
