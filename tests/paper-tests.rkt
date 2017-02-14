#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)
;; (require video/lib) ; playlist-append
;; (require rackunit "test-utils.rkt")

;; tests from paper examples

;; TODO:
;; 2017-02-10: "length" properly not working? #:len testing disabled
;; 2017-02-07: swipe transition not working

(define circ-png "circ.png")
(define vid-mp4 "vid.mp4")
(check-type circ-png : String)
(check-type vid-mp4 : String)

;; fig1 -----------------------------------------------------------------------

(define g (color "green"))
(define g1 (color "green" #:length 1))
(check-type g : Producer)
(check-not-type g : (Producer 1))
(check-type g1 : (Producer 1))
(check-type g1 : (Producer 2))
(check-type g1 : Producer)

(define blue-clip (color "blue" #:length 8))
(check-type blue-clip : (Producer 8))

;; TODO: define-lifting not working for typed define
(define (blue-length -> Int) (get-property blue-clip "length" 'int))
(check-type (blue-length) : Int)

;; TODO: eval-syntax length arg?
(check-type (image circ-png #:length (/ (blue-length) 8)) : Producer)

(check-type (composite-transition 0 0 3/4 3/4) : Transition)
;; ;(check-transition? (swipe-transition #:direction 'up #:length 2)) ; TODO
(check-type (fade-transition #:length 2) : Transition)

(check-type
 (multitrack
  (image circ-png #:length (/ (blue-length) 8))
  (composite-transition 0 0 3/4 3/4)
  blue-clip
  #:length 5)
 : Producer)

(check-type
 (multitrack
  (image circ-png #:length (/ (blue-length) 8))
  (composite-transition 0 0 3/4 3/4)
  blue-clip
  #:length 5)
 : (Producer 5))

(check-type (clip vid-mp4 #:length 3) : (Producer 3))

; other examples, section 4 ---------------------------------------------------
(check-type (color "blue" #:length 2) : (Producer 2))
(check-type (clip vid-mp4 #:start 100 #:end 103) : (Producer 3))
(check-type (image circ-png #:length 1) : (Producer 1))
(check-type (blank 2) : (Producer 2))
(define circ-img (image circ-png))
(define vid-clip (clip vid-mp4)) ; length = 139
(check-type circ-img : Producer)
(check-type vid-clip : Producer)
;; TODO
;(check-type vid-clip : (Producer 139))
(check-type (playlist circ-img vid-clip) : Producer)
(check-type (playlist (blank 2) circ-img vid-clip) : Producer)

;; TODO: shapes and colors defined after use
(define shapes (playlist circ-img vid-clip))
(define colors (playlist (color "red") (color "blue")))
(check-type shapes : Producer)
(check-type colors : Producer)
(check-type (playlist-append shapes colors) : Producer)
(check-type (playlist g1) : (Producer 1))
(check-type (playlist blue-clip) : (Producer 8))
(check-type (playlist-append (playlist g1) (playlist blue-clip)) : (Producer 9))

;; (check-producer
;;  (playlist (image circ-png #:length 3)
;;            ;(swipe-transition #:direction 'bottom #:duration 2)
;;            (fade-transition #:length 2)
;;            (clip vid-mp4 #:length 3)))
;; ; #:len 4) ; expect 4, currently 6

;; (check-producer
;;  (playlist (image circ-png #:length 3)
;;            (clip vid-mp4 #:length 3)))
;; ; #:len 6) ; expect 6, currently 8

;; (check-producer
;;  (playlist
;;   (image circ-png #:length 2)
;;   (fade-transition #:length 1)
;;   (color "blue" #:length 2)
;;   (fade-transition #:length 2)
;;   (clip vid-mp4 #:start 0 #:end 2))
;;  #:len 5)

;; ;; multitracks
;; (check-producer
;;  (multitrack
;;   (clip vid-mp4)
;;   (composite-transition 0 0 3/4 3/4)
;;   (image circ-png))
;;  #:len inf)

;; (check-producer
;;  (multitrack
;;   (clip vid-mp4)
;;   (composite-transition 0 0 1/2 1/2)
;;   (multitrack
;;    (image circ-png)
;;    (composite-transition 0 1/2 1/2 1/2)
;;    (color "green")))
;;  #:len inf)

;; ;; defines are after use
;; (check-producer
;;  (multitrack
;;   circ bg green-color
;;   #:transitions
;;   (list (composite-transition 0 0 1/2 1/2 #:top circ #:bottom bg)
;;         (composite-transition 1/2 0 1/2 1/2 #:top blue-color #:bottom bg)
;;         (composite-transition 0 1/2 1/2 1/2 #:top green-color #:bottom bg))))
;; (define bg (clip vid-mp4))
;; (define circ (image circ-png))
;; (define green-color (color "green"))
;; (define blue-color (color "blue"))

;; (check-producer? (swiping-playlist (image circ-png) (color "green")))
;; (check-producer? (swiping-playlist (color "green") (clip vid-mp4)))
;; (define swiping-playlist
;;   (λ (a b)
;;     (playlist a b
;;               #:transitions
;;               (list
;;                (composite-transition 0 0 1/2 1/2
;;                                      #:top a
;;                                      #:bottom b)))))

;; ;; filters
;; (check-producer? (scale-filter (image circ-png) 1 3))

;; ;; props
;; (check-producer?
;;  (multitrack
;;   rect-clip
;;   (composite-transition
;;    0
;;    (if (get-property rect-clip "bottom?") 1/2 0)
;;    1/2 1/2)
;;   (image circ-png)))
;; (define rect-clip (set-property (clip vid-mp4) "bottom?" #t))
;; (check-equal? (get-property rect-clip "bottom?") #t)

;; ;(include-video "green.vid")

;; ;; racketcon
;; (define (make-speaker-slides-composite sp sl)
;;   (multitrack sp sl logo bg
;;               #:transitions
;;               (list (composite-transition 0 0 3/10 1 #:top sp #:bottom bg)
;;                     (composite-transition 0 1/2 3/10 1 #:top logo #:bottom bg)
;;                     (composite-transition 1/3 0 2/3 1 #:top sl #:bottom bg))))
;; (define logo (image circ-png))
;; (define sp (blank 100))
;; (define sl (blank 100))
;; ;(define bg (color "blue")) ; already defined

;; ;; TODO: should this work? (defines at end)
;; #;(define (make-talk-video main-talk)
;;   ;; defines are after playlist
;;   (playlist begin-clip
;;             (fade-transition 200)
;;             main-talk
;;             (fade-transition 200)
;;             end-clip)
;;   (define begin-clip (image circ-png #:length 500))
;;   (define end-clip (image circ-png #:length 500)))

;; (define (make-talk-video main-talk)
;;   ;; defines should be after playlist?
;;   (define begin-clip (image circ-png #:length 500))
;;   (define end-clip (image circ-png #:length 500))
;;   (playlist begin-clip
;;             (fade-transition #:length 200)
;;             main-talk
;;             (fade-transition #:length 200)
;;             end-clip))

;; ; TODO: add filters
;; (define (attach-audio v a o)
;;   (define cleaned-audio
;;     (attach-filter
;;      a
;;      #;(project-filter #:end offset)
;;      #;(envelope-filter 50 #:direction 'in)
;;      #;(envelope-filter 50 #:direction 'out)))
;;   (multitrack v cleaned-audio #:length (get-property v "length" 'int)))

;; ;; TODO: use define*
;; (define (make-conf-talk sp sl a o)
;;   (define X (make-speaker-slides-composite sp sl))
;;   (define Y (make-talk-video X))
;;   (define v (make-talk-video Y))
;;   (attach-audio v a o))

;; (check-producer?
;;  (make-conf-talk (blank 100) (blank 100) (blank 100) 0))
