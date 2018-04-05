#lang typed/video
(require turnstile/rackunit-typechecking)

;; (check-type (color "green") : Producer)
;; (check-type (color "green") : (Producer 10)) ; shorted ok
(color "green")
