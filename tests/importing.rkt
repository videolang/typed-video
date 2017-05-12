#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)
(require-vid "blank20.rkt")
(check-type (external-video "poly.rkt") : (Producer 0))
(check-type (playlist (external-video "poly.rkt")) : (Producer 0))
;; #:start too high
(typecheck-fail
 (external-video "poly.rkt" #:start 10 #:end 20)
 #:with-msg (add-escs "expected (Producer 20), given (Producer 0)"))
;; #:end too high
(typecheck-fail
 (external-video "poly.rkt" #:start 0 #:end 6)
 #:with-msg (add-escs "expected (Producer 6), given (Producer 0)"))
(check-type (external-video "blank20.rkt") : (Producer 20))
(check-type (external-video "blank20.rkt" #:start 5 #:end 11) : (Producer 6))
;; #:end too high
(typecheck-fail
 (external-video "blank20.rkt" #:start 5 #:end 21)
 #:with-msg (add-escs "expected (Producer 21), given (Producer 20)"))
; start > end
(typecheck-fail
 (external-video "blank20.rkt" #:start 6 #:end 5)
 #:with-msg (add-escs "type mismatch: expected 6, given 5\n  expression: 5"))
(check-type vid : (Producer 20))
(typecheck-fail (external-video "non-exist.rkt")
                #:with-msg "cannot open module file")
