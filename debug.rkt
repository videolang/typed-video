#lang racket

(require
  '#%expobs
  syntax/modcode)

(define (expand/observe stx)
  (parameterize ([current-expand-observe
                  (lambda (event-type stxobj)
                    (when (or #;(equal? event-type 'lift-expr)
                              (equal? event-type 0)
                              (equal? event-type 'visit))
;                          (writeln event-type)
                          (writeln stxobj)))])
    (expand-syntax stx)))

(define rel-path (vector-ref (current-command-line-arguments) 0))

(expand/observe
  (get-module-code
    (build-path (current-directory) rel-path)
    #:choose (lambda _ 'src)
    #:compile (lambda (stx) stx)))
