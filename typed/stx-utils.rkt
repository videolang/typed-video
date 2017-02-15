#lang racket/base
(require syntax/parse syntax/stx macrotypes/stx-utils)
(provide (all-defined-out))

(define (stx+ ns)
  (apply + (map ; extract quoted numbers
            (syntax-parser [(_ x) (stx->datum #'x)])
            (stx->list ns))))
