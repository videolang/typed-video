#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (color "red" #:length 75) : (Producer 75))
(check-type (fade-transition #:length 25) : (Transition 25))
(check-type (clip "vid.mp4" #:start 50 #:end 100) : (Producer 50))
(check-type (fade-transition #:length 25) : (Transition 25))
(check-type (color "blue" #:length 75) : (Producer 75))

(check-type
 (playlist
  (color "red" #:length 75)
  (fade-transition #:length 25)
  (clip "vid.mp4" #:start 50 #:end 100)
  (fade-transition #:length 25)
  (color "blue" #:length 75))
 : (Producer 150))

(color "red" #:length 75)
(fade-transition #:length 25)
(clip "vid.mp4" #:start 50 #:end 100)
(fade-transition #:length 25)
(color "blue" #:length 75)
