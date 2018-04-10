#lang racket
(require (for-syntax syntax/parse racket/syntax syntax/stx))
(require (prefix-in v: racket))
(provide #%module-begin #%app provide
         (rename-out [my-define define]
                     [typed-datum #%datum]))

(begin-for-syntax

  (define (new-eval t)
    (syntax-parse (local-expand t 'expression null)
      [t #:do[(printf "EVALING: ~a\n" (syntax->datum #'t))
              (printf "with ty: ~a\n" (syntax-property #'t ':))]
         #:when #f #'(void)]
      [t+
       #:do[(define k-as-ty (syntax-property #'t+ ':))]
       #:when k-as-ty
       k-as-ty]
      [((~literal #%plain-app) (~literal list) n)
       (local-expand #`(list #,(new-eval #'n)) 'expression null)]))
  )

(define-syntax my-define
  (syntax-parser
    [(_ x e)
     #:with ty #`(list #,(local-expand (new-eval #'e) 'expression null))
     #'(define-syntax x (new-eval #'ty))
     ;; #'(define-syntax x
     ;;     (local-expand #`(list #,(new-eval #'ty)) 'expression null))
     ]))
   
(define-syntax typed-datum
  (syntax-parser
    [(_ . n:integer)  ; use singleton types
     (syntax-property #'(v:#%datum . n) ': #'n)]))
