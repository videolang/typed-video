#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (clip "vid.mp4" #:start 50 #:end 150) : (Producer 100))
(check-type
 (playlist
  (blank 40)
  (color "red"))
 : Producer)
(check-type
 (multitrack
  (clip "vid.mp4" #:start 50 #:end 150))
 : (Producer 100))
(check-type
 (multitrack
  (playlist
   (blank 40)
   (color "red")))
 : Producer)
(check-type
 (multitrack
  (clip "vid.mp4" #:start 50 #:end 150)
  (playlist
   (blank 40)
   (color "red")))
 : (Producer 100))

(multitrack
 (clip "vid.mp4" #:start 50 #:end 150)
 (playlist
  (blank 40)
  (color "red")))
