#lang racket/base
(require syntax/parse syntax/stx macrotypes/stx-utils)
(provide (all-defined-out))

 ; extract list of quoted numbers
(define (stx->nums stx)
  (map
   (syntax-parser [(_ x) (stx->datum #'x)]
                  [n:integer (stx-e #'n)])
   (stx->list stx)))

(define (stx+ ns)    (apply + (stx->nums ns)))
(define (stx- ns)    (apply - (stx->nums ns)))
(define (stx/ ns)    (apply / (stx->nums ns)))
(define (stx-max ns) (apply max (stx->nums ns)))
(define (stx-min ns) (apply min (stx->nums ns)))

(define stx-e syntax-e)
