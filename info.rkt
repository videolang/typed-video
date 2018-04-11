#lang info
(define collection 'multi)
(define deps '("base" "video" "turnstile"))

(define test-omit-paths
  '("debug.rkt"))

(define compile-omit-paths
  '("tests/"
    "examples/"))
