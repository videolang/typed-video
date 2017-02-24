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
(define (stx>= ns)   (apply >= (stx->nums ns)))
(define (stx- ns)    (apply - (stx->nums ns)))
(define (stx/ ns)    (apply / (stx->nums ns)))
(define (stx-max ns) (apply max (stx->nums ns)))
(define (stx-min ns) (apply min (stx->nums ns)))

(define stx-e syntax-e)

(define (stx-filter-out-false . stxs)
  (filter
   (λ (xs) (andmap (λ (x) (and x (stx-e x))) xs))
   (apply map list (map stx->list stxs))))

(define (add-stx-props stx ks vs)
  (for/fold ([stx stx]) ([k (in-stx-list ks)]
                         [v (in-stx-list vs)])
    (define k* (string->symbol (stx-e k))) ; must be symbol, to get properly transferred around
    (define v* (stx-e v))
    (syntax-property stx k* v*)))
