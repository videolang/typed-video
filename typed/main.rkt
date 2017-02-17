#lang racket/base

(provide (all-from-out "video.rkt")
         (rename-out [~module-begin #%module-begin]))
(require (except-in "video.rkt" #%module-begin)
         (prefix-in tv: "video.rkt")
         (prefix-in ru: turnstile/examples/tests/rackunit-typechecking)
         (prefix-in r: racket/base)
         (prefix-in core: video/core)
         (prefix-in v: video)
         racket/list
         ;(except-in pict clip frame blank)
         ;racket/draw
         (for-syntax ;(prefix-in v: video/base)
                     racket/base
                     racket/syntax
                     syntax/parse
                     syntax/parse/lib/function-header
                     syntax/kerncase))

(define-syntax (~module-begin stx)
  (syntax-parse stx
    [(_ id:id post-process exprs . body)
     #'(r:#%module-begin
        (video-begin id post-process exprs . body))]))

#;(define-syntax (λ/video stx)
  (syntax-parse stx
    [(_ args:function-header . body)
     #'(λ args (video-begin "λ/video" values () . body))]))

(begin-for-syntax
  (define tv-move-ids
    (list #'tv:define #'tv:require))
  (define tv-ids
    (append
     tv-move-ids
     (list #'tv:multitrack #'tv:clip)))
  (define ru-ids
    (list #'ru:check-type #'ru:check-not-type #'ru:typecheck-fail)))
(define-syntax (video-begin stx)
  (syntax-parse stx
    #;[(_ "λ/video" post-process exprs)
     #`(post-process (playlist . #,(reverse (syntax->list #'exprs))))]
    [(_ id:id post-process exprs)
     #`(r:begin
        (r:define id
         (v:#%app post-process
          (v:#%app v:playlist . #,(reverse (syntax->list #'exprs)))))
         (r:provide id))]
    [(_ id post-process exprs . body)
     (syntax-parse #'body
       [(b1 . body)
        (define expanded
          (local-expand
           #'b1 'module
           (append
            (kernel-form-identifier-list)
            (list #'provide #'require)
            tv-ids ru-ids)))
        (syntax-parse expanded
          #:literals (tv:begin)
          [(tv:begin b ...)
           #'(video-begin id post-process exprs b ... . body)]
          [(id* . rest) ; this bit taken from scribble
           #:when (and (identifier? #'id*)
                       (ormap (lambda (kw) (free-identifier=? #'id* kw))
                              (append tv-move-ids
                              (syntax->list #'(define-values
                                                define-syntaxes
                                                begin-for-syntax
                                                module
                                                module*
                                                #%require
                                                #%provide
                                                #%declare)))))
           #`(r:begin #,expanded (video-begin id post-process exprs . body))]
          [_
           #`(video-begin id post-process (#,expanded . exprs) . body)])])]))
