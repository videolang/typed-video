#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)
(check-type (blank 1) : (Producer 1))
(check-type (blank 1) : (Producer 2))
(check-not-type (blank 3) : (Producer 2))
(typecheck-fail (Producer Int) #:with-msg "expected exact-nonnegative-integer")
(check-type (blank (+ 1 2)) : Producer)
(check-not-type (blank (+ 1 2)) : (Producer 3))

(define (f1 [p : Producer] -> Producer) p)
(check-type (f1 (blank 10)) : Producer)

(define (f2 [p : (Producer 10)] -> (Producer 10)) p)
(check-type (f2 (blank 10)) : (Producer 10))
(check-type (f2 (blank 10)) : Producer)
(check-type (f2 (blank 9)) : (Producer 10))
(check-not-type (f2 (blank 9)) : (Producer 9))
(typecheck-fail (f2 (blank 11))
 #:with-msg "expected \\(Producer 10\\), given \\(Producer 11\\)")
(check-type (f2 (f2 (blank 10))) : (Producer 10))

;; check consistent output type
;; shorter not ok
(typecheck-fail/toplvl
 (define (f3 [p : (Producer 10)] -> (Producer 9)) p)
 #:with-msg "expected \\(Producer 9\\), given \\(Producer 10\\)")

;; longer ok
(define (f4 [p : (Producer 10)] -> (Producer 11)) p)
(check-type (f4 (blank 10)) : (Producer 11))
(check-not-type (f4 (blank 10)) : (Producer 10))

(define (f5 [p : (Producer 10)] -> Producer) p)
(check-type (f5 (blank 10)) : Producer)
(check-not-type (f5 (blank 10)) : (Producer 10))
