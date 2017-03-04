#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)
(require-vid "blank20.rkt")
(check-type (include-video "poly.rkt") : (Producer 0))
(check-type (playlist (include-video "poly.rkt")) : (Producer 0))
(check-type (include-video "poly.rkt" #:start 10 #:end 20) : (Producer 10))
(check-type vid : (Producer 20))
