#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;; more constraint testing

;; make sure dont get ambiguous binding err
;; (between n in Producer and C?)

;(define (f1 {n1} [p1 : (Producer n1)] -> (Producer n1)) p1)
