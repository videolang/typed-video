#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;; type-eval tests

(define bl1 (blank 100))
(check-type bl1 : (Producer 100))
(define bl2 (blank (producer-length bl1)))
(check-type bl2 : (Producer 100))

(define bl3 (blank (+ 1 2)))
(check-type bl3 : (Producer 3))

(define bl4 (blank (+ 1 (producer-length bl3))))
(check-type bl4 : (Producer 4))

;; TODO: current gives runtime exception due to bug
;; runtime result of (producer-length bl4) is incorrectly 1
(check-type (blank (/ (producer-length bl4) 4)) : (Producer 1))
