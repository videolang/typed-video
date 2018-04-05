#lang racket

(require
  '#%expobs
  syntax/modcode)

(define (expand/observe stx)
  (parameterize ([current-expand-observe (lambda (x y)
                                           (when (equal? x 'visit) #;(= x 0) ;(= x 0)
;                                             (writeln x)
                                             (writeln y)))])
    (expand-syntax stx)))

(define rel-path (vector-ref (current-command-line-arguments) 0))

(expand/observe
  (get-module-code
    (build-path (current-directory) rel-path)
    #:choose (lambda _ 'src)
    #:compile (lambda (stx) stx)))
