#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;(check-type (external-video "2-colorfade.rkt") : (Producer 125))

(external-video "2-colorfade.rkt")
