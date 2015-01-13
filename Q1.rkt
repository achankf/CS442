#lang racket

; wraps values as lists (if the item is a term, then it's already a list)
(define (wrapValueAsList item)
  (cond
    [(list? item) item]
    [else (list item)]
    )
  )

; handles the iszero term case. this is mutually recusive with evalTerm
(define (handleIsZero iszero)
  (let ([arg (wrapValueAsList (evalTerm (second iszero)))])
    (match (first arg)
      ['zero '(true)]
      ['succ '(false)]
      [_ (error "handleIsZero: unreachable")])
    )
  )

; handles the pred term case. this is mutually recusive with evalTerm (thus, also handleNv)
(define (handlePred nv)
  (let ([nvFixed (wrapValueAsList (evalTerm (second nv)))])
    (printf "second: ~a ~a (first nvFixed):~a\n" nvFixed (rest nvFixed) (first nvFixed))
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero nvFixed] ; nvFixed is zero
              ['succ (evalTerm (second nvFixed))] ; pop a succ from the remaining nv
              [_ (error "non-number")]
              )])
    ))

; handles the nv term case. this is mutually recusive with evalTerm
(define (handleNv nv)
  (let ([nvFixed (wrapValueAsList nv)])
    (printf "Got: ~a\n" nvFixed)
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero (list 'zero)]
              ['succ (list 'succ (evalTerm (second nvFixed)))]
              ['pred (handlePred nvFixed)]
              [_ (error "non-number")]
              )])
    ))

; if case. this is mutually recusive with evalTerm
(define (handleIf term)
  (let ([t (evalTerm (second term))])
    (match t
      ['(true) (evalTerm (list-ref term 3))]
      ['(false) (evalTerm (list-ref term 5))]
      [_ (error "non-Boolean")]
      )))

; "manager" function that potentially call helpers for results
(define (evalTerm term)
  (let ([fixedTerm (wrapValueAsList term)])
    (match (first fixedTerm)
      
      ; cases: matching values
      ['zero (list 'zero)]
      ['true (list 'true)]
      ['false (list 'false)]
      
      ; cases: matching terms
      ['if (handleIf fixedTerm)]
      ['succ (handleNv fixedTerm)]
      ['pred (handleNv fixedTerm)]
      ['iszero (handleIsZero fixedTerm)]
      
      [_ (error "evalTerm: unreachable, unexpected keyword found")])
    ))

; wrapper for evalTerm
(define (uae-eval term)
  (evalTerm term))

;; valid expressions
;(uae-eval '(if (if true then (if true then true else false) else false) then false else (succ zero)))
;(uae-eval '(if (if true then (if true then true else false) else false) then (succ (succ (zero))) else (succ zero)))
;(uae-eval '(true))
;(uae-eval '(zero))
;(uae-eval 'true)
;(uae-eval 'zero)
;(uae-eval '(if (iszero zero) then (succ zero) else zero)) ; '(succ zero)
;(uae-eval '(if (iszero (succ zero)) then (succ zero) else zero)) ; 'zero
;(uae-eval '(if (iszero (pred (pred (pred (succ (succ zero)))))) then (succ zero) else zero)) ; '(succ zero)
;(uae-eval '(pred zero))
;(uae-eval '(pred (pred (pred (succ (succ zero))))))
;(uae-eval '(pred (succ (pred (succ (succ (pred (succ (succ zero)))))))))
;(uae-eval '(iszero zero))
;(uae-eval '(iszero (succ zero)))
;(uae-eval '(iszero (succ (pred zero)))) ; false
;(uae-eval '(iszero (pred (succ zero)))) ; true
;(uae-eval '(iszero (pred (succ (if (if true then (if true then false else false) else false) then false else (succ zero)))))) ; false
;(uae-eval '(iszero (pred (succ (if (if true then (if true then false else false) else false) then false else (pred (succ zero))))))) ; true

;; invalid arguments
;(uae-eval '(iszero (succ true)))
;(uae-eval '(if zero then true else false))
;(uae-eval '(iszero true))
;(uae-eval '(pred (succ (pred (succ (succ (pred (succ (succ false)))))))))
;(uae-eval '(iszero (pred (succ (if (if true then (if true then true else false) else false) then false else (succ zero))))))
