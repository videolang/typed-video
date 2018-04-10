#lang typed/video
;; (require turnstile/examples/tests/rackunit-typechecking)

(define g75 (color "green" #:length 75))
;; (check-type g75 : (Producer 75))
(define fade25 (fade-transition #:length 25))
;; (check-type fade25 : (Transition 25))
(define b75 (color "blue" #:length 75))
;; (check-type b75 : (Producer 75))
;; (check-type (playlist g75 fade25 b75) : (Producer 125))
g75
fade25
b75
;(color "green" #:length 75)
