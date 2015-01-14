#lang racket

; wraps values as lists (if the item is a term, then it's already a list)
(define (wrapValueAsList item)
  (cond
    [(list? item) item]
    [else (list item)]
    )
  )

; handles the nv term case. this is mutually recusive with evalTerm
(define (handleIsZero nv)
  (let ([arg (wrapValueAsList (evalTerm (second nv)))])
    (match (first arg)
      ['zero 'true]
      ['succ 'false]
      [_ (error "non-number")])
    )
  )

; handles the pred term case. this is mutually recusive with evalTerm (thus, also handleNv)
(define (handlePred nv)
  (let ([nvFixed (wrapValueAsList (evalTerm (second nv)))])
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero 'zero] ; nvFixed is zero
              ['succ (evalTerm (second nvFixed))] ; pop a succ from the remaining nv
              [_ (error "non-number")]
              )])
    ))

; handles the succ term case. this is mutually recusive with evalTerm (thus, also handleNv)
(define (handleSucc nv)
  (let ([nvFixed (wrapValueAsList (evalTerm (second nv)))])
    ;(printf "handleSucc: ~a\n" nvFixed)
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero (list 'succ 'zero)] ; nvFixed is zero
              ['succ (list 'succ nvFixed)] ; pop a succ from the remaining nv
              [_ (error "non-number")]
              )])
    ))

; handles the nv term case. this is mutually recusive with evalTerm
(define (handleNv nv)
  (let ([nvFixed (wrapValueAsList nv)])
    ;(printf "Nv: ~a\n" nvFixed)
    (cond
      [(empty? nvFixed) null]
      [else (match (first nvFixed)
              ['zero 'zero]
              ['succ (handleSucc nvFixed)]
              ['pred (handlePred nvFixed)]
              [_ (error "non-number")]
              )])
    ))

; if case. this is mutually recusive with evalTerm
(define (handleIf term)
  (let ([t (evalTerm (second term))])
    ;(printf "t:~a term:~a | ~a | ~a\n" t term (list-ref term 3) (list-ref term 5))
    (match t
      ['true (evalTerm (list-ref term 3))]
      ['false (evalTerm (list-ref term 5))]
      [_ (error "non-Boolean")]
      )))

; "manager" function that potentially call helpers for results
(define (evalTerm term)
  (let ([fixedTerm (wrapValueAsList term)])
    ;(printf "term: ~a\n" term)
    (match (first fixedTerm)
      
      ; cases: matching values
      ['zero 'zero]
      ['true 'true]
      ['false 'false]
      
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

;; simple test method
;(define (test a b)
;  (printf "test: a:~a b:~a\n" a b)
;  (if (equal? a b) #t (error "failed")))
;
;; the example
;(test (uae-eval '(if (iszero zero) then (succ zero) else zero)) '(succ zero))
;
;; valid expressions
;(test (uae-eval  '(if true then true else false)) 'true)
;(test (uae-eval  '(if false then true else false)) 'false)
;(test (uae-eval  '(pred (succ zero))) 'zero)
;(test (uae-eval  '(succ (succ zero))) '(succ (succ zero)))
;(test (uae-eval '(if (if true then (if true then true else false) else false) then false else (succ zero))) 'false)
;(test (uae-eval '(if (if true then (if true then true else false) else false) then (succ (succ zero)) else (succ zero))) '(succ (succ zero)))
;(test (uae-eval 'true) 'true)
;(test (uae-eval 'false) 'false)
;(test (uae-eval 'zero) 'zero)
;(test (uae-eval '(if (iszero zero) then (succ zero) else zero)) '(succ zero))
;(test (uae-eval '(if (iszero (succ zero)) then (succ zero) else zero)) 'zero)
;(test (uae-eval '(if (iszero (pred (pred (pred (succ (succ zero)))))) then (succ zero) else zero)) '(succ zero))
;(test (uae-eval '(pred zero)) 'zero)
;(test (uae-eval '(pred (pred (pred (succ (succ zero)))))) 'zero)
;(test (uae-eval '(pred (succ (pred (succ (succ (pred (succ (succ zero))))))))) '(succ (succ zero)))
;(test (uae-eval '(iszero zero)) 'true)
;(test (uae-eval '(iszero (succ zero))) 'false)
;(test (uae-eval '(iszero (succ (pred zero)))) 'false)
;(test (uae-eval '(iszero (pred (succ zero)))) 'true)
;(test (uae-eval '(iszero (pred (succ (if (if true then (if true then false else false) else false) then false else (succ zero)))))) 'false)
;(test (uae-eval '(iszero (pred (succ (if (if true then (if true then false else false) else false) then false else (pred (succ zero))))))) 'true)
;
;; invalid arguments
;(uae-eval '(iszero (succ true)))
;(uae-eval '(if zero then true else false))
;(uae-eval '(iszero true))
;(uae-eval '(pred (succ (pred (succ (succ (pred (succ (succ false)))))))))
;(uae-eval '(iszero (pred (succ (if (if true then (if true then true else false) else false) then false else (succ zero))))))
;(uae-eval '(pred false))
