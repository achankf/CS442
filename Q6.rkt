#lang racket

(require test-engine/racket-tests)

(struct fun (param body) #:transparent)
(struct app (fn arg) #:transparent)
(struct rec (vars exps bdy) #:transparent)
(struct iff (test texp fexp) #:transparent)
(struct bin-op (op arg1 arg2) #:transparent)
(struct un-op (op arg) #:transparent)
(define-struct closure (ast env) #:transparent)

;; parse: s-expression -> AST

(define (parse sx)
  (match sx
    [`(with ,vars ,exp) (closure (parse exp) vars)]
    [`(if ,exp ,texp ,fexp) (iff (parse exp) (parse texp) (parse fexp))]
    [`(fun ,args ,bdy) 
     (cond [(not (equal? (length (remove-duplicates args)) (length args))) (error "duplicate")])
     (fun args (parse bdy))]
    
    ; unary operators
    [`(mt? ,exp) (un-op 'mt? (parse exp))]
    [`(zero? ,exp) (un-op 'zero? (parse exp))]
    [`(fst ,exp) (un-op 'fst (parse exp))]
    [`(rst ,exp) (un-op 'rst (parse exp))]
    
    ; binary operators
    [`(+ ,exp1 ,exp2) (bin-op '+ (parse exp1) (parse exp2))]
    [`(- ,exp1 ,exp2) (bin-op '- (parse exp1) (parse exp2))]
    [`(* ,exp1 ,exp2) (bin-op '* (parse exp1) (parse exp2))]
    [`(/ ,exp1 ,exp2) (bin-op '/ (parse exp1) (parse exp2))]
    [`(kons ,exp1 ,exp2) (bin-op 'kons (parse exp1) (parse exp2))]
    
    [`(rec ,exp) (un-op exp (parse exp))]
    [(? list?) (app (parse (first sx)) (map parse (rest sx)))]
    [x x]))

;; A substitution is a (list n v), where n is a symbol and v is a value.

;; An environment (env) is a list of substitutions.

;; An AST is a fun or an app or a var (symbol)

(define (interp-bin-op env op exp1 exp2)
  (printf "interp-bin-op: env:~a op:~a exp1:~a exp2:~a\n" env op exp1 exp2)
  (let ([eval1 (interp exp1 env)]
        [eval2 (interp exp2 env)])
    (match op
      ['+ (+ eval1 eval2)]
      ['- (- eval1 eval2)]
      ['* (* eval1 eval2)]
      ['/ (/ eval1 eval2)]
      ['kons `(kons ,eval1 ,eval2)]
      ))
  )

(define (bool value)
  (if value 'tru 'fls))

(define (interp-un-op env op exp)
  (printf "interp-un-op: env:~a op:~a exp1:~a\n" env op exp)
  (let ([reducedValue (interp exp env)])
    (match op
      ['mt? (bool (equal? reducedValue 'mt))]
      ['zero? (bool (equal? reducedValue 0))]
      ['fst (second reducedValue)]
      ['rst (third reducedValue)]
      ))
  )

;; interp: AST env -> closure

(define (zip key value) (map list key value))

(define (racket-bool value)
  (if (equal? value 'tru) true false)
  )

(define (interp ast env)
  (printf "ast:~a env:~a\n" ast env)
  (match ast
    ; constants
    ['mt 'mt]
    ['fls 'fls]
    ['tru 'tru]
    [(? number?) ast]
    
    ; operators
    [(un-op op exp) (interp-un-op env op exp)]
    [(bin-op op exp1 exp2) (interp-bin-op env op exp1 exp2)]
    
    ; expressions
    [(rec vars exps bdy) empty] ; todo
    [(iff test texp fexp) 
     (if (racket-bool (interp test env)) (interp texp env) (interp fexp env))]
    [(fun v bdy) (closure ast env)]
    [(closure cast cenv) (interp cast (append env cenv))]
    [(app fun-exp arg-exp)
     (match (interp fun-exp env)
       [(closure (fun param body) cl-env)
        (cond [(not (equal? (length param) (length arg-exp))) (error "wrong number")])
        ; since functions now have multiple parameters, so create an env for the paramaters and then append it to the closure's env
        (let ([param-env (zip param (map (lambda (exp) (interp exp env)) arg-exp))])
          (interp body (append param-env cl-env)))]
       [_ (error "not a function")]
       )]
    [x (second (assoc x env))]))

;; please comment out or change the name of this function in
;; code submitted to Marmoset

;(define (run sexp) (closure-ast (interp (parse sexp) empty)))

; binary ops
(check-expect (parse '(+ 1 2)) (bin-op '+ 1 2))
(check-expect (parse '(- 1 2)) (bin-op '- 1 2))
(check-expect (parse '(* 1 2)) (bin-op '* 1 2))
(check-expect (parse '(/ 1 2)) (bin-op '/ 1 2))
(check-expect (parse '(kons 123 mt)) (bin-op 'kons 123 'mt))
(check-expect (parse '(kons 123 (kons 234 mt))) 
              (bin-op 'kons 123 (bin-op 'kons 234 'mt)))
(check-expect (parse '(+ (* 3 9) (/ 2 (- 3 1))))
              (bin-op '+ (bin-op '* 3 9) (bin-op '/ 2 (bin-op '- 3 1))))

(check-expect (interp (parse '(+ 1 2)) '()) 3)
(check-expect (interp (parse '(+ (* 3 9) (/ 2 (- 3 1)))) '()) 28)
(check-expect (interp (parse '(kons 123 (kons 234 mt))) '())
              '(kons 123 (kons 234 mt)))

; unary ops
(check-expect (parse '(mt? mt)) (un-op 'mt? 'mt))
(check-expect (parse '(zero? 343)) (un-op 'zero? 343))
(check-expect (parse '(fst (kons 99 mt))) (un-op 'fst (bin-op 'kons 99 'mt)))
(check-expect (parse '(rst (kons 99 mt))) (un-op 'rst (bin-op 'kons 99 'mt)))

(check-expect (interp (parse '(mt? mt)) '()) 'tru)
(check-expect (interp (parse '(mt? (kons 99 mt))) '()) 'fls)
(check-expect (interp (parse '(zero? 0)) '()) 'tru)
(check-expect (interp (parse '(zero? 1)) '()) 'fls)
(check-expect (interp (parse '(zero? (- (+ 12 12) 24))) '()) 'tru)
(check-expect (interp (parse '(fst (kons 99 (kons 99 mt)))) '()) 99)
(check-expect (interp (parse '(rst (kons 99 (kons 99 mt)))) '()) '(kons 99 mt))
(check-expect (interp (parse '(rst (rst (kons 99 (kons 99 mt))))) '()) 'mt)
(check-expect (interp (parse '(mt? (rst (rst (kons 99 (kons 99 mt)))))) '()) 'tru)
(check-expect (interp (parse '(kons 123 (rst (rst (kons 99 (kons 99 mt)))))) '()) '(kons 123 mt))

; const
(check-expect (parse 33) 33)
(check-expect (parse 'tru) 'tru)
(check-expect (parse 'fls) 'fls)

(check-expect (interp (parse 'tru) empty) 'tru)
(check-expect (interp (parse 'fls) empty) 'fls)
(check-expect (interp (parse 2343) empty) 2343)

; iff
(check-expect (parse '(if tru 123 435)) (iff 'tru 123 435))
(check-expect (interp (parse '(if tru 123 435)) '()) 123)
(check-expect (interp (parse '(if tru (rst (kons 99 (kons 99 mt))) 435)) '()) '(kons 99 mt))
(check-expect (interp (parse '(if fls 123 (+ (* 3 9) (/ 2 (- 3 1))))) '()) 28)

; app

(check-expect (interp (parse '((fun (a b c d e f g) (kons a (kons b (kons c (kons d (kons e (kons f (kons g mt))))))))
                               123 tru fls 5 65 7 9)) '())
              '(kons 123 (kons tru (kons fls (kons 5 (kons 65 (kons 7 (kons 9 mt))))))))

; others
(check-expect (parse '(fun (x y) x)) (fun '(x y) 'x))
(check-expect (parse '(zero? 0)) (un-op 'zero? 0))
(check-expect (parse '(with ((x 10) (y 20)) x)) (closure 'x '((x 10) (y 20))))
(check-expect (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) z))))
              (closure (closure (bin-op '* (bin-op '+ 'x 'y) 'z) '((z 4))) '((x 10) (y 20))))
(check-expect (interp (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) z)))) '()) 120)
(check-expect (interp (parse '(fun (x y) x)) '()) (closure (fun '(x y) 'x) '()))
(check-expect (interp (parse '((fun (x y) (kons x y)) 123 (rst (kons 123 mt)))) '()) '(kons 123 mt))

(test)