#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type (clip "vid.mp4" #:start 50 #:end 200) : (Producer 151))
(check-type
 (playlist
  (blank 40)
  (color "red"))
 : Producer)
(check-type
 (multitrack
  (clip "vid.mp4" #:start 50 #:end 200))
 : (Producer 151))
(check-type
 (multitrack
  (playlist
   (blank 40)
   (color "red")))
 : Producer)
(check-type
 (multitrack
  (clip "vid.mp4" #:start 50 #:end 200)
  (playlist
   (blank 40)
   (color "red")))
 : (Producer 151))

(multitrack
 (clip "vid.mp4" #:start 50 #:end 200)
 (playlist
  (blank 40)
  (color "red")))
