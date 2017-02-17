#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (clip "vid.mp4") : (Producer 139))
(clip "vid.mp4")
