#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (grayscale-filter (clip "vid.mp4")) : (Producer 139))
(grayscale-filter (clip "vid.mp4"))
