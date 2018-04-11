#lang racket/base

(provide (all-from-out "video.rkt")
         (rename-out [~module-begin #%module-begin]))
(require (except-in "video.rkt" #%module-begin)
         (prefix-in tv: "video.rkt")
         (prefix-in ru: turnstile/rackunit-typechecking)
         (prefix-in r: racket/base)
         racket/list
         (for-syntax racket/base
                     racket/syntax
                     macrotypes/stx-utils
                     syntax/parse
                     syntax/parse/lib/function-header
                     syntax/kerncase)
         (only-in turnstile expand/stop typeof erased current-use-stop-list?))

;; typed/video/lang/reader.rkt uses implicit (#%mod-beg vid values () . body)
(define-syntax (~module-begin stx)
  (syntax-parse stx
    [(_ id:id post-process exprs . body)
     #'(r:#%module-begin
        (video-begin id post-process exprs . body))]))

;; TODO: add λ/video
#;(define-syntax (λ/video stx)
  (syntax-parse stx
    [(_ args:function-header . body)
     #'(λ args (video-begin "λ/video" values () . body))]))

(begin-for-syntax
  (define tv-ids-to-move
    (list #'tv:define #'tv:require #'tv:require-vid))
  (define tv-ids
    (append
     tv-ids-to-move
     (list #'tv:multitrack))) ; TODO: should all all tv ids here?
  (define ru-ids
    (list #'ru:check-type #'ru:check-not-type #'ru:typecheck-fail)))

(require (for-syntax racket/pretty))
(define-syntax (video-begin stx)
  (syntax-parse stx
    #;[(_ "λ/video" post-process exprs) ; TODO
     #`(post-process (playlist . #,(reverse (syntax->list #'exprs))))]
    [(_ id:id post-process exprs) ; base case, no more body exprs to check
     #:with id-ty (format-id #'id "~a-ty" #'id)
     #:with id-ty2 (format-id #'id "~a-ty2" #'id)
     #:with (id* id-ty* id-ty2*) (generate-temporaries #'(id id-ty id-ty2))
     ;; typecheck the "top level" playlist
     ;; - doing full expansion, instead of expand/stop,
     ;;   may mess up the order of lifted expressions produced by contract-out
     ;;   eg, #lang typed/video (color "green" #:length 1) (define blue-clip (color "blue" #:length 8))

     ;; body may have non-producers, like rackunit statements;
     ;; so top-level-playlist filters these out
     ;; TODO: for now, dont post-process
     ;; (post-process should wrap this top-level-playlist)
     #:with p #`(tv:top-level-playlist . #,(reverse (syntax->list #'exprs)))
     #:with p- (expand/stop #'p)
               ;(local-expand/capture-lifts #'p 'expression (list #'erased))
     ;; #:do[(displayln "expanding in video begin:")]
     ;; #:do[(pretty-print (syntax->datum #'p-))]
     #:with (~and (~Producer (_ n)) ty) (typeof #'p-);(syntax-property #'p- ':) ; typeof
     #`(r:begin
        (r:define id* p-) ; this is the implicit "vid" binding

        ;; next two defs are vid's type; provide type as both:
        ;; - macro (used by require-vid)
        ;; - length num (used via dynamic-require in external-video)
        (r:define-syntax id-ty* (make-variable-like-transformer #'ty))
        ;; TODO:
        ;; I wanted to provide the whole stx obj instead of just length, but
        ;; I got stx= errors when trying to compare imported vs module-local stx
        ;; eg (=? (Producer 0) (Producer 0))
        ;; - even #%app is not the same
        ;; - this is probably the same issue William ran into
        (r:define id-ty2* (r:#%datum . n))

        ;; use rename-out so require can use raw vid w/o renaming
        ;; (since vid can't be used within its own module anyways)
        ;; - should untyped video do this as well?
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
;        (pretty-print (stx->datum expanded))
        (syntax-parse expanded
          #:literals (tv:begin)
          [(tv:begin b ...)
           #'(video-begin id post-process exprs b ... . body)]
          [(id* . _) ; this bit taken from scribble
           #:when (and (identifier? #'id*)
                       (ormap (lambda (kw) (free-identifier=? #'id* kw))
                              (append tv-ids-to-move
                                      (syntax->list
                                       #'(define-values
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
