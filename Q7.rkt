#lang racket

(require test-engine/racket-tests)

;; helper methods

(define (app-reducible? left right)
  (or 
   (match left
     [`(λ ,_ ,_) #t]
     [`(,left ,right) (app-reducible? left right)]
     [_ #f])
   (match right
     [`(λ ,_ ,term) (reducible? term)]
     [`(,left ,right) (app-reducible? left right)]
     [_ #f])
   )
  )

(define (reducible? expr)
  (printf "reducible? ~a\n" expr)
  (match expr
    ;; unlike call-by-value, we need to reduce "things" inside an abstraction
    [`(λ ,var ,term) (reducible? term)]
    [`(,left ,right) (app-reducible? left right)]
    ;; cannot reduce a variable further
    [var #f]
    )
  )

;; Evaluation rules:
;;    

(define (reduce expr)
  (printf "reduce expr:~a\n" expr)
  (match expr
    [`(λ ,var ,term) `(λ ,var ,(normalize term))]
    [`(,t1 ,t2)
     (match (reduce t1)
       [`(λ ,var ,term) (subst var t2 term)]
       [_ expr])
     ]
    [var var]
    )
  )

;; main methods

;; test whether a given variable is fresh in expr
(define (is-fresh x expr)
  ;(printf "is-fresh: x:~a expr:~a\n" x expr)
  (match expr
    ;; x is not a variable in the paramater
    [`(λ ,var ,term) (and 
                      (not (equal? x var))
                      (is-fresh x term))]
    [`(,t1 ,t2) (and (is-fresh x t1)
                     (is-fresh x t2))]
    ;; base case: not a free variable
    [var (not (equal? x var))]
    ))

;; Perform alpha-conversion on the expr for a target variable x.
;;
;; This method recurse deeply into each subterm -- it does not 
;; matter if the subterm has another binding for x, because
;; variables are bound by the closest scope.
;;
;; Here, a fresh variable is an integer that does not 
;; clash with existing variables in expr and its "parents" --
;; through the use of non-free.
;;
;; Only "free variables" are left as-is -- though it's likely that expr
;; is a sub-expression of a larger expression, which binds x.
(define (a-convert x expr non-free)
  (printf "a-convert: x:~a expr:~a non-free:~a\n" x expr non-free)
  (letrec (
           ;; generate a fresh variable based on recusion and counting up from 0 (i.e. O(n^2) algorithm)
           [find-fresh
            (lambda (expr non-free counter)
              (if (and (not (member counter non-free))
                       (is-fresh counter expr))
                  counter
                  (find-fresh expr non-free (add1 counter))))]
           
           ;; replace all x's in all subterms of expr with y
           [deep-replace 
            (lambda (x y expr)
              (match expr
                [`(λ ,var ,term) `(λ ,(if (equal? var x) y var) ,(deep-replace x y term))]
                [`(,t1 ,t2) `(,(deep-replace x y t1) ,(deep-replace x y t2))]
                [var (if (equal? var x) y var)]
                ))])
    (let ([fresh (find-fresh expr non-free 0)])
      (deep-replace x fresh expr)
      )))

;; Perform substitution based on page 71's substituion rule
(define (subst x N M)
  (letrec ([subst-helper
            (lambda (x N M non-free)
              (printf "subst x:~a N:~a M:~a non-free:~a\n" x N M non-free)
              (match M
                [`(λ ,var ,term)
                 ;; alpha convert every abstraction, so that the condition (y not equals x and y not in FV(s)) holds
                 (match (a-convert var M non-free)
                   [`(λ ,var ,term) `(λ ,var ,(subst-helper x N term (cons var non-free)))]
                   )
                 ]
                [`(,t1 ,t2) `(,(subst x N t1) ,(subst x N t2))]
                [var 
                 (printf "\t\tsubst-var: x:~a var:~a\n" x var)
                 (cond 
                   [(equal? var x) N]
                   [else M])]
                ))])
    (subst-helper x N M '())))

(define (normalize expr)
  (printf "normalize expr:~a\n" expr)
  (cond
    [(reducible? expr) (normalize (reduce expr))]
    [else expr]))

;; test cases (manually verified)
;(a-convert 'x '(λ y (λ z x)) '(x))
;(a-convert 'z '(λ y (λ z z)) '())
;(a-convert 'z '(λ y (λ z y)) '())
;(a-convert 'z '(λ y (λ z y)) '())
;(a-convert 'z '(λ y (λ z (λ z z))) '())
;(a-convert 'z '((λ y (λ z (λ z z))) (λ y (λ z (λ z z)))) '())
;(a-convert 'z '(((λ y (λ z (λ a a))) (λ y (λ z (λ c z)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ z z))))) '())
;(a-convert 'y (a-convert 'z '(λ y (λ z y)) '()) '())
;(a-convert 'y (a-convert 'c (a-convert 'a (a-convert 'z '(((λ y (λ z (λ a a))) (λ y (λ z (λ c z)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ z z))))) '()) '()) '()) '())
;(a-convert 'y '(λ y y) '())

;; test cases

(check-expect (subst 'a 'b 'c) 'c)
(check-expect (subst 'a 'b 'a) 'b)
(check-expect (subst 'x 'y '(λ x x)) '(λ 0 0))
(check-expect (subst 'x 'z '(λ y x)) '(λ 0 z))
(check-expect (subst 'x 'z '(λ y y)) '(λ 0 0))
(check-expect (subst 'x 'z '(λ y (λ z x))) '(λ 0 (λ 1 z)))

(check-expect (subst 'x 'z '(((λ y (λ z (λ a a))) (λ y (λ z (λ c z)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ z z))))))
              '(((λ 0 (λ 1 (λ 2 2))) (λ 0 (λ 1 (λ 2 1)))) ((λ 0 (λ 1 (λ 2 2))) (λ 0 (λ 1 (λ 2 2))))))

;(subst 'x '(λ jjjj c) '(((λ y (λ z (λ a a))) (λ y (λ z (λ c x)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ x x))))))

;(subst 'c 'yyyyyy (subst 'x '(λ jjjj c) '(((λ y (λ z (λ a a))) (λ y (λ z (λ c x)))) ((λ y (λ z (λ z z))) (λ y (λ z (λ x x)))))))

(check-expect (is-fresh 'x '(λ y (λ z x))) #f)
(check-expect (is-fresh 'x '(λ y (λ z z))) #t)
(check-expect (is-fresh 'x '(λ y (λ z y))) #t)
(check-expect (is-fresh 'x '((λ y (λ z x)) (λ z x))) #f)
(check-expect (is-fresh 0 '(λ y (λ 0 x))) #f)
(check-expect (is-fresh 1 '(λ y (λ 0 x))) #t)

(check-expect (a-convert 'x '(λ y (λ z x)) '()) '(λ y (λ z 0)))

(check-expect (normalize '(λ y (λ z x))) '(λ y (λ z x)))
(check-expect (normalize '((λ y x) (λ x x))) 'x)

;; should be infinite loop in call-by-value, but fine in normal order
(check-expect (normalize '((λ y x) ((λ x (x x)) (λ x (x x))))) 'x)
(check-expect (normalize '((λ y (λ y y)) ((λ x (x x)) (λ x (x x))))) '(λ 0 0))

;; reuse Q2's test cases
(check-expect (normalize '(λ x x)) '(λ x x))
(check-expect (normalize '(λ x (x x))) '(λ x (x x)))
(check-expect (normalize '(λ x (x (λ y y)))) '(λ x (x (λ y y))))
(check-expect (normalize '(λ x (λ y y))) '(λ x (λ y y)))
(check-expect (normalize '((λ x x) (λ x (λ b (λ y y))))) '(λ x (λ b (λ y y))))
(check-expect (normalize '((λ x x) ((λ y y) (λ z z)))) '(λ z z))
(check-expect (normalize '((λ y y) (λ z z))) '(λ z z))
(check-expect (normalize '((λ y (y y)) (λ z z))) '(λ z z))
(check-expect (normalize '((λ x (λ a a)) (λ y y))) '(λ 0 0))
(check-expect (normalize '((λ x (λ a x)) (λ y y))) '(λ 0 (λ y y)))
(check-expect (normalize '(((λ x x) (λ x x)) (λ x x))) '(λ x x))
(check-expect (normalize '((λ x (λ a (x x))) (λ y y))) '(λ 0 (λ y y)))
(check-expect (normalize '((λ x (λ a (x x))) (λ y ((λ z y) (λ z y))))) '(λ 0 (λ y y)))
(check-expect (normalize '((λ x (λ a (x x))) ((λ z z) (λ b b)))) '(λ 0 (λ b b)))
(check-expect (normalize '((λ x (λ a (a a))) ((λ z z) (λ b b)))) '(λ 0 (0 0)))
(check-expect (normalize '((λ x x) ((λ x x) (λ z ((λ x x) z))))) '(λ z z))
(check-expect (normalize '((λ x (λ x (λ x x))) (λ x x))) '(λ 0 (λ 1 1)))
(check-expect (normalize '((λ x (λ y (λ x x))) (λ z z))) '(λ 0 (λ 1 1)))
(check-expect (normalize '((λ x (λ x (λ x x))) (λ z z))) '(λ 0 (λ 1 1)))
(check-expect (normalize '((λ x (λ y (λ x (λ y y)))) (λ z z))) '(λ 0 (λ 1 (λ 2 2))))
(check-expect (normalize '((λ x (λ y (λ x (λ x x)))) (λ z z))) '(λ 0 (λ 1 (λ 2 2))))
(check-expect (normalize '((λ x (λ y (λ x (x x)))) (λ z z))) '(λ 0 (λ 1 (1 1))))

(normalize '((λ x (λ y (λ z (x x)))) (λ z z)))

(normalize '((λ x (λ z (x x))) (λ z z)))

;; additional ones
(check-expect (normalize '((λ x (x x)) (λ z z))) '(λ z z))
(check-expect (normalize '((λ x x) ((λ x x) (λ z ((λ x c) z))))) '(λ z c))

(test)
