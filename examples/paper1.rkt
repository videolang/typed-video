#lang typed/video
(require turnstile/rackunit-typechecking)

(check-type (color "green" #:length 1) : (Producer 1))

(check-type
 (multitrack
  (image "circ.png" #:length (producer-length blue-clip))
  (composite-transition 0 0 3/4 3/4)
  blue-clip)
 : (Producer 8))

(check-type (fade-transition #:length 2) : (Transition 2))

(check-type (clip "vid.mp4" #:length 3) : (Producer 3))

(color "green" #:length 1)
(multitrack
 (image "circ.png" #:length (producer-length blue-clip))
 (composite-transition 0 0 3/4 3/4)
 blue-clip)

; (swipe-transition #:direction 'up #:length 2) ; TODO
(fade-transition #:length 2)

(clip "vid.mp4" #:length 3)

(define blue-clip (color "blue" #:length 8))

