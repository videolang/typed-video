#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(check-type 
 (multitrack
  blocks
  circ
  red
  #:transitions (list (composite-transition 0.1 0.1 0.3 0.3
                                            #:top circ
                                            #:bottom blocks)
                      (composite-transition 0.6 0.6 0.2 0.2
                                            #:top red
                                            #:bottom blocks)))
 : (Producer 101))
(check-not-type
 (multitrack
  blocks
  circ
  red
  #:transitions (list (composite-transition 0.1 0.1 0.3 0.3
                                            #:top circ
                                            #:bottom blocks)
                      (composite-transition 0.6 0.6 0.2 0.2
                                            #:top red
                                            #:bottom blocks)))
 : (Producer 102))

(multitrack
 blocks
 circ
 red
 #:transitions (list (composite-transition 0.1 0.1 0.3 0.3
                                           #:top circ
                                           #:bottom blocks)
                     (composite-transition 0.6 0.6 0.2 0.2
                                           #:top red
                                           #:bottom blocks)))

(define blocks (clip "vid.mp4" #:start 50 #:end 150))
(define circ (image "circ.png" #:length 200))
(define red (color "red"))
