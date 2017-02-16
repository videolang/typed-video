#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)
(check-type (blank 1) : (Producer 1))
(check-type (blank 1) : (Producer 0)) ; shorter type ok
(check-not-type (blank 1) : (Producer 2)) ; longer type not ok
(typecheck-fail (Producer Int) #:with-msg "expected exact-nonnegative-integer")
(check-not-type (blank (+ 1 2)) : Producer)
(check-type (blank (+ 1 2)) : (Producer 3))

(define (f1 [p : Producer] -> Producer) p)
(check-type (f1 (color "green")) : Producer)

(define (f2 [p : (Producer 10)] -> (Producer 10)) p)
(check-type (f2 (color "green")) : (Producer 10))
(check-type (f2 (blank 10)) : (Producer 10))
(check-not-type (f2 (blank 10)) : Producer)
(typecheck-fail (f2 (blank 9)) ; too short
 #:with-msg "expected \\(Producer 10\\), given \\(Producer 9\\)")
(check-type (f2 (blank 11)) : (Producer 10)) ; longer ok
(check-type (f2 (f2 (blank 10))) : (Producer 10))

;; check consistent output type
;; shorter not ok
(typecheck-fail/toplvl
 (define (f3 [p : (Producer 10)] -> (Producer 11)) p)
 #:with-msg "expected \\(Producer 11\\), given \\(Producer 10\\)")

(define (f4 [p : (Producer 10)] -> (Producer 11)) (playlist (blank 1) p))
(check-type (f4 (blank 10)) : (Producer 11))
(check-type (f4 (blank 11)) : (Producer 11))

;; shorter ok
(define (f5 [p : (Producer 10)] -> (Producer 9)) p)
(check-type (f5 (blank 10)) : (Producer 9))
(check-not-type (f5 (blank 10)) : (Producer 10))
