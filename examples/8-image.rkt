#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (image "circ.png" #:length 200) : (Producer 200))
(image "circ.png" #:length 200)
