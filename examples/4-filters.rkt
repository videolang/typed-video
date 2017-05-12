#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (grayscale-filter) : Filter)
(check-type (attach-filter (clip "vid.mp4") (grayscale-filter)) : (Producer 139))
(attach-filter (clip "vid.mp4") (grayscale-filter))
