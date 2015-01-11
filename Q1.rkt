#lang racket

(define (wrapSingleTermAsList item)
  (cond
    [(list? item) item]
    [else (list item)]
    )
  )

(define (handleIsZero iszero)
  
  (unless (eq? (first iszero) 'iszero)
    (error "handleIsZero: sanity check failed -- first term should be 'iszero"))
  
  (let ([arg (wrapSingleTermAsList (handleNv (second iszero)))])
    (match (first arg)
      ['zero '(true)]
      ['succ '(false)]
      [_ (error "handleIsZero: unreachable")])
    )
  )

(define (handleNv nv)
  (let ([nvFixed (wrapSingleTermAsList nv)])
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero (list 'zero)]
              ['succ (list 'succ (handleNv (second nvFixed)))]
              [_ (error "non-number")]
              )])
    ))

(define (handleIf term)
  (let ([t (evalTerm (second term))])
    (match t
      ['(true) (evalTerm (list-ref term 3))]
      ['(false) (evalTerm (list-ref term 5))]
      [_ (error "non-Boolean")]
      )))

(define (evalTerm term)
  (let ([fixedTerm (wrapSingleTermAsList term)])
    (cond
      [(match (first fixedTerm)
         ['zero (list 'zero)]
         ['true (list 'true)]
         ['false (list 'false)]
         ['if (handleIf fixedTerm)]
         ['succ (handleNv fixedTerm)]
         ['iszero (handleIsZero fixedTerm)]
         [_ (error "evalTerm: unreachable")])]
      )))

(define (uae-eval term)
  (evalTerm term))

;; valid expressions
;(evalTerm '(if (if true then (if true then true else false) else false) then false else (succ zero)))
;(evalTerm '(if (if true then (if true then true else false) else false) then (succ (succ (zero))) else (succ zero)))
;(evalTerm '(true))
;(evalTerm '(zero))
;(evalTerm '(if (iszero zero) then (succ zero) else zero))

;; invalid arguments
;(evalTerm '(iszero (succ true)))
;(evalTerm '(if zero then true else false))
;(evalTerm '(iszero true))
