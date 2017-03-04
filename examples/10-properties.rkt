#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)


(typecheck-fail
 (clip "vid.mp4"
      #:start 50
      #:end (if (equal? (get-property v-clip "vid-key") "block")
                200
                51))
 #:with-msg
 (add-escs "clip: type mismatch: expected 151, given 139"))
(check-type
 (clip "vid.mp4"
      #:start 50
      #:end (if (equal? (get-property v-clip "vid-key") "block")
                150
                51))
 : (Producer 101))
(check-not-type
 (clip "vid.mp4"
       #:start 50
       #:end (if (equal? (get-property v-clip "vid-key") "block")
                 150
                 51))
 : Producer)
(define v-clip
  (clip "vid.mp4"
        #:properties (hash "vid-key" "block")))
