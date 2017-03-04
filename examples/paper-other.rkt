#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (color "green") : Producer)
(check-type (color "blue" #:length 2) : (Producer 2))
(check-not-type (color "blue" #:length 2) : (Producer 3))
(check-type (clip "vid.mp4" #:start 100 #:end 103) : (Producer (- 103 100)))
(check-type (clip "vid.mp4" #:start 100 #:end 103) : (Producer 3))
(check-not-type (clip "vid.mp4" #:start 100 #:end 103) : (Producer 4))

(check-type
 (playlist
  (color "green")
  (color "blue" #:length 2)
  (clip "vid.mp4" #:start 100 #:end 103))
 : Producer)
(color "green")
(color "blue" #:length 2)
(clip "vid.mp4" #:start 100 #:end 103)
