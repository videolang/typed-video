#lang video
(require video/core)
(color "green" #:length 1)

(multitrack
 (image "circ.png" #:length (blue-length))
 (composite-transition 0 0 3/4 3/4)
 blue-clip)

; (swipe-transition #:direction 'up #:length 2) ; TODO
;(fade-transition #:length 2)

(clip "vid.mp4" #:length 3)

;(define blue-clip (color "blue" #:length 8))
(define blue-clip (color "blue"))
(define (blue-length) 8)