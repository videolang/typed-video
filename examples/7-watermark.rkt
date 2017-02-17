#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type
 (multitrack
  (clip "vid.mp4")
  (composite-transition 0.1 0.1 0.3 0.3)
  (color "red"))
 : (Producer 139))
(check-not-type ; make sure type is not inf
 (multitrack
  (clip "vid.mp4")
  (composite-transition 0.1 0.1 0.3 0.3)
  (color "red"))
 : (Producer 140))

(multitrack
 (clip "vid.mp4")
 (composite-transition 0.1 0.1 0.3 0.3)
 (color "red"))
