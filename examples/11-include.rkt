#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (include-video "2-colorfade.rkt") : (Producer 125))

(include-video "2-colorfade.rkt")
