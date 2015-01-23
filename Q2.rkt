#lang racket

;;;;;;;;;;;;;;;;;;;;;;;; closed?

; member returns the found object, but we need a predicate that returns a boolean for decision making
(define (contains? v list)
  (ormap (lambda(x) (equal? v x)) list))

; helper method -- takes a list of variables (under the scope of current lambda and above) and a term
(define (closedHelper varList term)
  ;(printf "closedHelper: varList:~a term:~a\n" varList term)
  (match term
    [(? symbol? v) (contains? v varList)]
    [(list 'λ v t) (closedHelper (cons v varList) t)]
    [(list t1 t2)  (and (closedHelper varList t1)
                        (closedHelper varList t2))]
    )
  )

(define (closed? term)
  (closedHelper '() term))

;;;;;;;;;;;;;;;;;;;;;;;; lc-cbv-eval

(define (recursive-replace target by list)
  (map 
   (lambda (x)
     (cond 
       [(equal? x target) by]
       [(list? x) (recursive-replace target by x)]
       [else x])) list))

(define (substitute-lambda parentX x1 t1 by)
  (match t1
    [(list 'λ x2 t2) 
     (cond
       [(equal? parentX x1) t1]
       [else (substitute t1 by)]
       )]
    ))

; note: t2 is already simplified; t1 might not
; substitute t2 into t1
(define (substitute t1 t2)
  (match t1
    [(list 'λ v t) 
     (match t
       [(? symbol?) t2]
       [(list 'λ xx tt) ;(substitute-lambda v xx tt t2)]
        (cond
          [(equal? v xx) t]
          [else (recursive-replace v t2 t)])]
       [(list _ _) (printf "c\n") (lc-cbv-eval (recursive-replace v t2 t))] ; needs to be re-evaulated because we may apply further reduction after application
       )]
    [(list t1left t1right) (substitute (substitute t1left t1right) t2)] ; left-hand-side is an application -- needs lots of simplification
    )
  )

(define (lc-cbv-eval term)
  (match term
    [(list 'λ _ _) term] ; base case -- in normal form; don't touch
    [(list t1 t2)  (substitute t1 (lc-cbv-eval t2))] ; case 2: application; also, don't touch t1 for now
    ))

; simple test method
(define (test a b)
  (printf "test: a:~a b:~a\n" a b)
  (if (equal? a b) #t (error "failed")))

; test cases for lc-cbv-eval
(test (lc-cbv-eval '(λ x x)) '(λ x x))
(test (lc-cbv-eval '(λ x (x x))) '(λ x (x x)))
(test (lc-cbv-eval '(λ x (x (λ y y)))) '(λ x (x (λ y y))))
(test (lc-cbv-eval '(λ x (λ y y))) '(λ x (λ y y)))
(test (lc-cbv-eval '((λ x x) (λ x (λ b (λ y y))))) '(λ x (λ b (λ y y))))
(test (lc-cbv-eval '((λ x x) ((λ y y) (λ z z)))) '(λ z z))
(test (lc-cbv-eval '((λ y y) (λ z z))) '(λ z z))
(test (lc-cbv-eval '((λ y (y y)) (λ z z))) '(λ z z))
(test (lc-cbv-eval '((λ x (λ a a)) (λ y y))) '(λ a a))
(test (lc-cbv-eval '((λ x (λ a x)) (λ y y))) '(λ a (λ y y)))
(test (lc-cbv-eval '(((λ x x) (λ x x)) (λ x x))) '(λ x x))
(test (lc-cbv-eval '((λ x (λ a (x x))) (λ y y))) '(λ a ((λ y y) (λ y y))))
(test (lc-cbv-eval '((λ x (λ a (x x))) (λ y ((λ z y) (λ z y))))) '(λ a ((λ y ((λ z y) (λ z y))) (λ y ((λ z y) (λ z y))))))
(test (lc-cbv-eval '((λ x (λ a (x x))) ((λ z z) (λ b b)))) '(λ a ((λ b b) (λ b b))))
(test (lc-cbv-eval '((λ x (λ a (a a))) ((λ z z) (λ b b)))) '(λ a (a a)))
(test (lc-cbv-eval '((λ x x) ((λ x x) (λ z ((λ x x) z))))) '(λ z ((λ x x) z)))
(test (lc-cbv-eval '((λ x (λ x (λ x x))) (λ x x))) '(λ x (λ x x)))

; test cases for closed?
(test (closed? 'x) #f)
(test (closed? '(λ x y)) #f)
(test (closed? '(λ x x)) #t)
(test (closed? '((a b) c)) #f)
(test (closed? '(x y)) #f)
(test (closed? '((λ x x) y)) #f)
(test (closed? '((λ x x) x)) #f)
(test (closed? '((λ x x) (λ x x))) #t)
(test (closed? '((λ x ((λ a a) (λ b b))) (λ x (λ variable variable)))) #t)
(test (closed? '((λ x ((λ a (a x)) (λ b (b x)))) (λ x (λ variable x)))) #t)
(test (closed? '((λ x ((λ a (a b)) (λ b (b x)))) (λ x (λ variable x)))) #f)
(test (closed? '((λ x ((λ a (a a)) (λ b (b x)))) (λ x (λ variable x)))) #t)
(test (closed? '((λ x ((λ a (a a)) (λ b (b a)))) (λ x (λ variable x)))) #f)
(test (closed? '((λ x ((λ a a) (λ b b))) (λ y (λ x variable)))) #f)
