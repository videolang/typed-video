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
                     macrotypes/stx-utils
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
    (list #'tv:define #'tv:require #'tv:require-vid))
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
     #:with id-ty (format-id #'id "~a-ty" #'id)
     #:with id-ty2 (format-id #'id "~a-ty2" #'id)
     #:with (id* id-ty* id-ty2*) (generate-temporaries #'(id id-ty id-ty2))
     #:with p- (local-expand
                 ;; TODO: for now, dont post-process since it's untyped
                 #`(tv:top-level-playlist . #,(reverse (syntax->list #'exprs)))
                 'expression null)
     #:with (~and (~Producer (_ n)) ty) (syntax-property #'p- ':)
     #`(r:begin
        (r:define id* p-)
        (r:define-syntax id-ty* (make-variable-like-transformer #'ty))
        ;; just provide the number
        ;; TODO: get stx= errors when trying to compare
        ;; imported vs module-local stx
        ;; eg (=? (Producer 0) (Producer 0))
        ;; - even #%app is not the same
        ;; - this is probably the same issue William ran into
        (r:define id-ty2* (r:#%datum . n))
        ;; provide type as both
        ;; - macro (used by require-vid)
        ;; - stx (used via dynamic-require in include-video)
        (r:provide (rename-out [id* id] [id-ty* id-ty]))
        (r:provide (rename-out [id-ty2* id-ty2])))]
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
