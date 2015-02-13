#lang racket

(require test-engine/racket-tests)

;; helper methods

(define (reducible? expr)
  (letrec (
           ;; test whether an application, separated by left and right, is reducible.
           [app-reducible?
            (lambda(left right)
              ;(printf "expr:~a parents:~a\n" expr parents)
              (or
               (match left
                 [`(λ ,_ ,_) #t]
                 [`(,t1 ,t2) (app-reducible? t1 t2)]
                 [_ #f])
               (match right
                 [`(λ ,_ ,term) (reducible? term)]
                 [`(,t1 ,t2) (app-reducible? t1 t2)]
                 [_ #f])
               ))
            ])
    ;(printf "reducible? ~a\n" expr)
    (match expr
      ;; unlike call-by-value, we need to reduce "things" inside an abstraction
      [`(λ ,var ,term) (reducible? term)]
      [`(,left ,right) (app-reducible? left right)]
      ;; cannot reduce a variable further
      [_ #f]
      )
    ))

(define (reduce expr)
  ;(printf "reduce expr:~a\n" expr)
  ;(printf ">>>>> ~a parents:~a\n" expr parents)
  (match expr
    [`(λ ,var ,term) `(λ ,var ,(reduce term))]
    [`((λ ,var ,term) ,t2) (subst var t2 term)]
    [`(,t1 ,t2)
     ;; at least one term must be reducible, because normalize guarantees that
     (if (reducible? t1) 
         `(,(reduce t1) ,t2)
         `(,t1 ,(reduce t2)))]
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
  ;(printf "subst x:~a N:~a M:~a \n" x N M)
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
;(reducible? '((λ x (x x)) (λ x (x x))))
;(reducible?  '(λ _v_21044 ((q _v_21044) ((λ a x) (λ a x)))))
;(reducible? '((λ x (y z)) ((λ x (x x)) (λ x (x x)))))
;(reducible? '((λ x (y z)) ((λ x (x x)) (λ x (x x)))))
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

;(normalize '((λ w (λ x ((λ z y) w))) ((λ x x) ((λ x (x x)) (λ x (x x))))))
(check-expect (normalize '((λ x (y z)) ((λ x (x x)) (λ x (x x))))) '(y z))
;(normalize '((λ x (λ x ((x y) z))) ((λ x (x x)) (λ x (x x)))))
(check-expect (normalize '((λ a (λ b (z b) a)) z)) '(λ b (z b) a))
;(normalize '((λ a (λ b ((q b) a))) ((λ a x) (λ a x))))

;; make sure the following don't terminates
;(normalize '((λ w (λ x ((x y) w))) ((λ x (x x)) (λ x (x x)))))
;(normalize '((λ w (λ x ((x y) w))) ((λ x (x x)) (λ x (x x)))))
;(normalize '((λ w (λ x ((z y) w))) ((λ x (x x)) (λ x (x x)))))
;(normalize '((λ w (λ x ((λ z y) w))) ((λ x (x x)) (λ x (x x)))))
;(normalize '((λ x (y x)) ((λ x (x x)) (λ x (x x)))))
;(normalize '(y ((λ x (x x)) (λ x (x x)))))
;(normalize '((λ x (x x)) (λ x (x x))))

(test)