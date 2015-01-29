#lang racket

(struct closure (abs env) #:transparent)

(define (search key env)
  (let ([found (assoc key env)])
    (printf "search: env:~a key:~a found:~a\n" env key found)
    (second found)))

(define (handleApplication t1closure t2closure)
  (printf "handleApplication:\n|\tt1closure:~a\n|\tt2closure~a\n" t1closure t2closure)
    (match (closure-abs t1closure)
      [(list 'λ x t) (evaluate t (cons (list x t2closure) (closure-env t1closure)))]
      ))

; "helper" that does the actual computation
(define (evaluate exp env)
  (printf "evaluate:\n|\texp:~a\n|\tenv:~a\n" exp env)
  (match exp
    [(? symbol?) (search exp env)] ; base case -- value
    [(list 'λ _ _) (closure exp env)] ; abstraction -- don't go further, stop here...
    [(list t1 t2) ; application
     (let ([t1closure (evaluate t1 env)]
           [t2closure (evaluate t2 env)])
       (handleApplication t1closure t2closure))] ; semantics say that t1closure's env will be used instead
    )
  )

; the name is too long, so this method serves as a wrapper to the actual codes
(define (lc-cbv-eval-env exp env)
  (evaluate exp env))

;;;;;;;; test cases

; simple test method
(define (test a b)
  (printf "test: a:~a b:~a\n" a b)
  (if (equal? a b) #t (error "failed")))

(test (lc-cbv-eval-env '(λ x x) '()) (closure '(λ x x) '()))
(test (lc-cbv-eval-env '((λ x x) (λ z z)) '()) (closure '(λ z z) '()))

; short-hand for tests
(define (value abs)
  (closure abs '()))

; short-hand wrapper for main function
(define (reduce exp)
  (lc-cbv-eval-env exp '()))

(reduce '((λ x x) (λ y y)))
(reduce '((λ x ((x (λ z z)) (λ a a))) (λ y y)))

; modified test suite from Q2
(test (reduce '(λ x x)) (value '(λ x x)))
(test (reduce '(λ x (x x))) (value '(λ x (x x))))
(test (reduce '(λ x (x (λ y y)))) (value '(λ x (x (λ y y)))))
(test (reduce '(λ x (λ y y))) (value '(λ x (λ y y))))
(test (reduce '((λ x x) (λ x (λ b (λ y y))))) (value '(λ x (λ b (λ y y)))))
(test (reduce '((λ x x) ((λ y y) (λ z z)))) (value '(λ z z)))
(test (reduce '((λ y y) (λ z z))) (value '(λ z z)))
(test (reduce '((λ y (y y)) (λ z z))) (value '(λ z z)))
(test (reduce '((λ x (λ a x)) (λ y y))) (closure '(λ a x) (list (list 'x (closure '(λ y y) '())))))
(test (reduce '((λ x (λ a a)) (λ y y))) (closure '(λ a a) (list (list 'x (closure '(λ y y) '())))))
(test (reduce '(((λ x x) (λ x x)) (λ x x))) (value '(λ x x)))
(test (reduce '((λ x (λ a (x x))) (λ y y))) (closure '(λ a (x x)) (list (list 'x (closure '(λ y y) '())))))
(test (reduce '((λ x (λ a (x x))) (λ y ((λ z y) (λ z y))))) (closure '(λ a (x x)) (list (list 'x (closure '(λ y ((λ z y) (λ z y))) '())))))
(test (reduce '((λ x (λ a (x x))) ((λ z z) (λ b b)))) (closure '(λ a (x x)) (list (list 'x (closure '(λ b b) '())))))
(test (reduce '((λ x (λ a (a a))) ((λ z z) (λ b b)))) (closure '(λ a (a a)) (list (list 'x (closure '(λ b b) '())))))
(test (reduce '((λ x x) ((λ x x) (λ z ((λ x x) z))))) (value '(λ z ((λ x x) z))))
(test (reduce '((λ x (λ x (λ x x))) (λ x x))) (closure '(λ x (λ x x)) (list (list 'x (closure '(λ x x) '())))))
(test (reduce '((λ x (λ y (λ x x))) (λ z z))) (closure '(λ y (λ x x)) (list (list 'x (closure '(λ z z) '())))))
(test (reduce '((λ x (λ x (λ x x))) (λ z z))) (closure '(λ x (λ x x)) (list (list 'x (closure '(λ z z) '())))))
(test (reduce '((λ x (λ y (λ x (λ y y)))) (λ z z))) (closure '(λ y (λ x (λ y y))) (list (list 'x (closure '(λ z z) '())))))
(test (reduce '((λ x (λ y (λ x (λ x x)))) (λ z z))) (closure '(λ y (λ x (λ x x))) (list (list 'x (closure '(λ z z) '())))))
(test (reduce '((λ x (λ y (λ x (x x)))) (λ z z))) (closure '(λ y (λ x (x x))) (list (list 'x (closure '(λ z z) '())))))

(test (evaluate '((λ x (x x)) x) (list (list 'x (closure '(λ y y) '())))) (value '(λ y y)))

(test (reduce '((λ x (λ y (λ x (x x)))) (λ z z))) (closure '(λ y (λ x (x x))) (list (list 'x (closure '(λ z z) '())))))
(test (reduce '(((λ x (λ y (λ x (x x)))) (λ z z)) (λ a a))) (closure '(λ x (x x)) (list (list 'y (closure '(λ a a) '())) (list 'x (closure '(λ z z) '())))))
(test (reduce '((((λ x (λ y (λ x (x x)))) (λ z z)) (λ a a)) (λ b b))) (closure '(λ b b) '()))