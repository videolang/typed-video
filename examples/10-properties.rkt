#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)


(check-type
 (clip "vid.mp4"
      #:start 50
      #:end (if (equal? (get-property v-clip "vid-key") "block")
                200
                51))
 : (Producer 151))
(check-not-type
 (clip "vid.mp4"
       #:start 50
       #:end (if (equal? (get-property v-clip "vid-key") "block")
                 200
                 51))
 : Producer)
(define v-clip
  (clip "vid.mp4"
        #:properties (hash "vid-key" "block")))
