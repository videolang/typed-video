#lang racket
(require (for-syntax syntax/parse racket/syntax syntax/stx))
(require (prefix-in v: racket))
(provide #%module-begin #%app provide #%datum
         (rename-out [my-define define]
                     #;[typed-datum #%datum]))

(begin-for-syntax

  (define (le e) (local-expand e 'expression null))
  (define (to e) (syntax-property e ':))
  #;(define (new-eval t)
    (syntax-parse (local-expand t 'expression null)
      [t #:do[(printf "EVALING: ~a\n" (syntax->datum #'t))
              (printf "with ty: ~a\n" (syntax-property #'t ':))]
         #:when #f #'(void)]
      [t+
       #:do[(define k-as-ty (syntax-property #'t+ ':))]
       #:when k-as-ty
       k-as-ty]
      #;[((~literal #%plain-app) (~literal list) n)
       (local-expand #`(list #,(new-eval #'n)) 'expression null)]))
  )

(define-syntax my-define
  (syntax-parser
    [(_ x e)
     ;     #:with ty #`(list #,(le (syntax-property (le #'e) ':)))
     ;     #:with e+ (le #'e)
     #:with e+ (syntax-property #'(v:#%datum . e) ': #'e)
     #:with ty #`(list e+)
;     #:with ty (le #'e)
;     #'(define-syntax x (new-eval #'ty))
     #'(define-syntax x
         (syntax-parse (le #'ty)
           [x
            #:do[(displayln #'x)]
            #:when #f #'(void)]
           [(_ _ n) (le #`(list #,(to (le #'n))))]))
     ]))
   
#;(define-syntax typed-datum
  (syntax-parser
    [(_ . n)  ; use singleton types
     (syntax-property #'(v:#%datum . n) ': #'n)]))
