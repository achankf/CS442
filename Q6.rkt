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

; length of (static-arg-length sx) <> length of sx implies (error "wrong number")
(define (static-arg-length sx)
  (cond 
    [(not (list? sx)) #f] ; not applicable -- this may be a function name, variable, etc.
    [else (match (first sx)
            ['with 3]
            ['if 4]
            ['fun 3]
            ['mt? 2]
            ['zero? 2]
            ['fst 2]
            ['rst 2]
            ['+ 3]
            ['- 3]
            ['* 3]
            ['/ 3]
            ['kons 3]
            ['rec 3]
            [_ #f] ; not applicable -- checks for application is deferred to runtime (or interp-time, if you like)
            )]
    ))

(define (make-env-out-of-vars vars)
  (map 
   (lambda(x) 
     (list (first x) (parse (second x)))) 
   vars))

(define (parse sx)
  ; error-checking
  (let ([len (static-arg-length sx)])
    (cond
      [(not len) (void)] ; don't care -- not applicable
      [(not (equal? len (length sx))) (error "wrong number")]))
  
  ; at this point, everything expect for "application" should have the correct number of arguments
  
  (match sx
    ; keywords
    [`(with ,vars ,exp) (closure (parse exp) (make-env-out-of-vars vars) )]
    [`(if ,exp ,texp ,fexp) (iff (parse exp) (parse texp) (parse fexp))]
    [`(fun ,args ,bdy) 
     (cond [(not (equal? (length (remove-duplicates args)) (length args))) (error "duplicate")])
     (fun args (parse bdy))]
    [`(rec ,bindings ,exp) (rec (make-env-out-of-vars bindings) 
                             (void) ; not used -- we make rec-exps an environment instead
                             (parse exp))]
    
    ; hardcode operators to leave rooms for custom-defined functions of arity 1 or 2
    
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
    
    ; application
    [(? list?) (app (parse (first sx)) (map parse (rest sx)))]
    
    ; var, const
    [x x]
    ))

;; A substitution is a (list n v), where n is a symbol and v is a value.

;; An environment (env) is a list of substitutions.

;; An AST is a fun or an app or a var (symbol)

(define (interp-bin-op env op exp1 exp2)
  (printf "interp-bin-op: env:~a op:~a exp1:~a exp2:~a\n\n" env op exp1 exp2)
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
  (printf "ast:~a env:~a\n\n" ast env)
  (match ast
    ; constants
    ['mt 'mt]
    ['fls 'fls]
    ['tru 'tru]
    [(list 'kons _ _) ast]
    [(? number?) ast]
    
    ; operators
    [(un-op op exp) (interp-un-op env op exp)]
    [(bin-op op exp1 exp2) (interp-bin-op env op exp1 exp2)]
    
    ; expressions
    [(rec vars exps bdy) (interp bdy (append vars env))]
    [(iff test texp fexp)
     (if (racket-bool (interp test env)) (interp texp env) (interp fexp env))]
    [(fun v bdy) (closure ast env)]
    [(closure cast cenv) (interp cast (append cenv env))]
    [(app fun-exp arg-exp)
     (match (interp fun-exp env)
       [(closure (fun param body) cl-env)
        (cond [(not (equal? (length param) (length arg-exp))) (error "wrong number")])
        ; since functions now have multiple parameters, so create an env for the paramaters and then append it to the closure's env
        (let ([param-env (zip param (map (lambda (exp) (interp exp env)) arg-exp))])
          (interp body (append param-env cl-env)))]
       [x (error "not a function")]
       )]
    [x (let ([found (assoc x env)])
         (cond [(not found) (error "undefined")])
         (match (second found)
           [(fun _ _) (interp (second (assoc x env)) env)] ; get function from environment
           [_ (interp (second (assoc x env)) env)]))] ; this may be a variable that can be further reduced
    ))

;; please comment out or change the name of this function in
;; code submitted to Marmoset

;(define (run sexp) (closure-ast (interp (parse sexp) empty)))

; let-rec
(check-expect
 (interp 
  (parse
   '(rec ([factorial (fun (n)
                          (if (zero? n) 1 (* n (factorial (- n 1)))))])
      (factorial 3)))
  '())
 6)

(check-expect
 (interp 
  (parse
   '(rec ([factorial (fun (n)
                          (if (zero? n) 1 (* n (factorial (- n 1)))))])
      (factorial 0)))
  '())
 1)

(check-expect
 (interp 
  (parse
   '(rec ([sum-1-to-n-helper (fun (n acc)
                                  (if (zero? n) acc (sum-1-to-n-helper (- n 1) (+ n acc))))]
          [sum-1-to-n (fun (n)
                           (sum-1-to-n-helper n 0))])
      (sum-1-to-n 10)))
  '())
 55)

(check-expect (interp (parse `(rec ((x (fun (z) y)) (a 1012) (y a)) (x 6446))) '()) 1012)

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
(check-expect (interp (parse '(with ((tail (kons 234 mt))) (kons 123 tail))) '())
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
(check-expect (interp (parse '((fun (x) x) y)) '((y 123))) 123)

; others
(check-expect (parse '(fun (x y) x)) (fun '(x y) 'x))
(check-expect (parse '(zero? 0)) (un-op 'zero? 0))
(check-expect (parse '(with ((x 10) (y 20)) x)) (closure 'x '((x 10) (y 20))))
(check-expect (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) z))))
              (closure (closure (bin-op '* (bin-op '+ 'x 'y) 'z) '((z 4))) '((x 10) (y 20))))
(check-expect (interp (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) z)))) '()) 120)
(check-expect (interp (parse '(fun (x y) x)) '()) (closure (fun '(x y) 'x) '()))
(check-expect (interp (parse '((fun (x y) (kons x y)) 123 (rst (kons 123 mt)))) '()) '(kons 123 mt))

(check-expect  (interp (parse '(with ((x 1) (y 2)) (fun (z) z))) '())
               (closure (fun '(z) 'z) '((x 1) (y 2))))
(check-expect (interp (parse '(fun (x) x)) '()) (closure (fun '(x) 'x) '()))

; errors

; undefined
(check-error (interp (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) unbound-variable)))) '()))

; wrong number -- too many arguments
(check-error (interp (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x y) z z z z z z z z z z)))) '()))
; wrong number -- too few arguments
(check-error (interp (parse '(with ((x 10) (y 20)) (with ((z 4)) (* (+ x) z)))) '()))

(test)