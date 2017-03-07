#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(define v (clip "vid.mp4"))
(check-type v : (Producer 139))
(typecheck-fail (cut-producer (blank 49) #:start 50)
 #:with-msg "expected 50, given 49")
(check-type (cut-producer v #:start 50) : (Producer 89))
(check-not-type (cut-producer v #:start 50) : Producer)

(cut-producer v #:start 50)
