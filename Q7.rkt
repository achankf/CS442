#lang racket

(require test-engine/racket-tests)

;; helper methods

(define (reducible? expr)
	(match expr
		[(? symbol?) expr]
		[`() expr]
	)
)

(define (reduce expr)
	expr)

;; main methods

(define (subst x N M)
	x)

(define (normalize expr)
	expr)

;; test cases

(define (a-equiv expr1 expr2)
	#t)

(check-expect true true);

(test)
