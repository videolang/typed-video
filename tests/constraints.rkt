#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;; more constraint testing

;; other interesting examples to try:
;;
;; (define (f {n} [p : (Producer (- n 1))] -> (Producer n)))
;; - does this reject all inputs?

;; producer-length
(check-type (producer-length (blank 10)) : 10)
(check-type (producer-length (blank 10)) : Nat)
(check-type (producer-length (blank 10)) : Int)

(define bl10 (blank 10))
(check-type bl10 : (Producer 10))
(typecheck-fail (Producer Nat) #:with-msg "expected expression of type Int, given Nat")

;; test singleton types
(check-type (blank (producer-length bl10)) : (Producer 10))
(check-type (blank (producer-length bl10)) : (Producer 9)) ; < ok
(check-not-type (blank (producer-length bl10)) : (Producer 11)) ; > not ok
(check-type (blank (+ 2 (producer-length bl10))) : (Producer 12))

(define bl10-len (producer-length bl10))
(check-type (blank bl10-len) : (Producer 10))

(define bl10-len+2 (+ 2 (producer-length bl10)))
(check-type (blank bl10-len+2) : (Producer 12))

(define bl10-len-2 (- (producer-length bl10) 2))
(check-type (blank bl10-len-2) : (Producer 8))

(define bl10-len2 (+ 2 (- (producer-length bl10) 2)))
(check-type (blank bl10-len2) : (Producer 10))

;; fails immediate Producer side-condition check
(typecheck-fail
 (blank -1)
 #:with-msg
 "constraints.rkt.*Producer: expression has type \\(Producer -1\\), which fails side-condition: \\(>= -1 0\\)")
(typecheck-fail (blank (- bl10-len 11))
 #:with-msg
 "constraints.rkt.*Producer: expression has type \\(Producer \\(- bl10-len 11\\)\\), which fails side-condition: \\(>= \\(- bl10-len 11\\) 0\\)")
(check-type (blank (- bl10-len 10)) : (Producer 0))
(check-type (blank (- bl10-len bl10-len)) : (Producer 0))

(check-type (multitrack bl10 #:length (- (producer-length bl10) 1)) : (Producer 9))
(check-type (multitrack bl10 #:length (- (producer-length bl10) 1))
            : (Producer (- (producer-length bl10) 1)))

(define (f1 {n1} [p1 : (Producer n1)] -> (Producer (- n1 5)))
  (multitrack p1 #:length (- (producer-length p1) 5)))

(check-type (f1 (blank 10)) : (Producer 5))
;; fails propagated Producer side-condition check
(typecheck-fail
 (f1 (blank 2))
 #:with-msg
 (add-escs
  "#%app: while applying fn f1;\nfailed condition: (>= (- (producer-length p1) 5) 0);\ninferred: n1 = 2;\nfor function type: (→ #:bind (n1) (Producer n1) (Producer (- n1 5)) #:when (>= (- (producer-length p1) 5) 0))"))
