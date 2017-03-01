#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;; checking err msgs

;; #:length, #:start, #:end should not be negative
(typecheck-fail
 (multitrack (blank 10)
             #:transitions (list (fade-transition #:length 1))
             #:length -1)
 #:with-msg "expected Nat, given -1")
(typecheck-fail (multitrack (blank 10) #:length -1)
                #:with-msg "expected Nat, given -1")
(typecheck-fail (color "green" #:length -1)
                #:with-msg "expected Nat, given -1")
(typecheck-fail (image "circ.png" #:length -1)
                #:with-msg "expected Nat, given -1")
(typecheck-fail (clip "vid.mp4" #:length -1)
                #:with-msg "expected Nat, given -1")
(typecheck-fail (clip "vid.mp4" #:start -1 #:end 10)
                #:with-msg "expected Nat, given -1")
(typecheck-fail (clip "vid.mp4" #:start 0 #:end -1)
                #:with-msg "expected Nat, given -1")
