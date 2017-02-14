#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

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
(check-type (playlist shapes colors) : Producer)
(check-type (playlist g1) : (Producer 1))
(check-type (playlist blue-clip) : (Producer 8))
(check-not-type (playlist blue-clip) : (Producer 7))
(check-type (playlist g1 blue-clip) : (Producer 9))
(check-not-type (playlist g1 blue-clip) : (Producer 8))
(check-type (playlist (playlist g1) (playlist blue-clip)) : (Producer 9))
(check-not-type (playlist (playlist g1) (playlist blue-clip)) : (Producer 8))
(check-type
 (playlist (image circ-png #:length 3)
           ;(swipe-transition #:direction 'bottom #:duration 2)
           (fade-transition #:length 2)
           (clip vid-mp4 #:length 3))
: (Producer 4))
(check-not-type
 (playlist (image circ-png #:length 3)
           ;(swipe-transition #:direction 'bottom #:duration 2)
           (fade-transition #:length 2)
           (clip vid-mp4 #:length 3))
: (Producer 3))

(check-type
 (playlist (image circ-png #:length 3)
           (clip vid-mp4 #:length 3))
 : (Producer 6))

(check-type
 (playlist
  (image circ-png #:length 2)
  (fade-transition #:length 1)
  (color "blue" #:length 2)
  (fade-transition #:length 2)
  (clip vid-mp4 #:start 0 #:end 2))
 : (Producer 3))
(check-not-type
 (playlist
  (image circ-png #:length 2)
  (fade-transition #:length 1)
  (color "blue" #:length 2)
  (fade-transition #:length 2)
  (clip vid-mp4 #:start 0 #:end 2))
 : (Producer 2))

;; multitracks
(check-type
 (multitrack
  (clip vid-mp4)
  (composite-transition 0 0 3/4 3/4)
  (image circ-png))
 : Producer)

(check-type
 (multitrack
  (clip vid-mp4)
  (composite-transition 0 0 1/2 1/2)
  (multitrack
   (image circ-png)
   (composite-transition 0 1/2 1/2 1/2)
   (color "green")))
 : Producer)

;; defines should be after use?
(define bg (clip vid-mp4))
(define circ (image circ-png))
(define green-color (color "green"))
(define blue-color (color "blue"))
(check-type
 (composite-transition 0 0 1/2 1/2 #:top circ #:bottom bg)
 : Transition)
(check-type
 (composite-transition 1/2 0 1/2 1/2 #:top blue-color #:bottom bg)
 : Transition)
(check-type
 (composite-transition 0 1/2 1/2 1/2 #:top green-color #:bottom bg)
 : Transition)
(check-type (list 1) : (Listof Int))
(check-type
 (list (composite-transition 0 0 1/2 1/2 #:top circ #:bottom bg)
       (composite-transition 1/2 0 1/2 1/2 #:top blue-color #:bottom bg)
       (composite-transition 0 1/2 1/2 1/2 #:top green-color #:bottom bg))
 : (Listof Transition))
(check-type
 (multitrack
  circ bg blue-color green-color
  #:transitions
  (list (composite-transition 0 0 1/2 1/2 #:top circ #:bottom bg)
        (composite-transition 1/2 0 1/2 1/2 #:top blue-color #:bottom bg)
        (composite-transition 0 1/2 1/2 1/2 #:top green-color #:bottom bg)))
 : Producer)

(define swiping-playlist
  (λ ([a : Producer] [b : Producer])
    (playlist a b
              #:transitions
              (list
               (composite-transition 0 0 1/2 1/2
                                     #:top a
                                     #:bottom b)))))
(check-type (swiping-playlist (image circ-png) (color "green")) : Producer)
(check-type (swiping-playlist (color "green") (clip vid-mp4)) : Producer)


;; filters
(check-type (scale-filter (image circ-png) 1 3) : Producer)

;; props
(define rect-clip (set-property (clip vid-mp4) "bottom?" #t))
;; TODO: how to do this?
(check-type (get-property rect-clip "bottom?" 'bool) : Bool -> #t)
(check-type
 (multitrack
  rect-clip
  (composite-transition
   0
   (if (get-property rect-clip "bottom?" 'bool) 1/2 0)
   1/2 1/2)
  (image circ-png))
 : Producer)

;(include-video "green.vid") ; TODO

;; racketcon
(define logo (image circ-png))
(define sp (blank 100))
(define sl (blank 100))
;(define bg (color "blue")) ; already defined
(define (make-speaker-slides-composite [sp : Producer] [sl : Producer] → Producer)
  (multitrack sp sl logo bg
              #:transitions
              (list (composite-transition 0 0 3/10 1 #:top sp #:bottom bg)
                    (composite-transition 0 1/2 3/10 1 #:top logo #:bottom bg)
                    (composite-transition 1/3 0 2/3 1 #:top sl #:bottom bg))))

(check-type make-speaker-slides-composite : (→ Producer Producer Producer))
;; TODO: should this work? (defines at end)
#;(define (make-talk-video main-talk)
  ;; defines are after playlist
  (playlist begin-clip
            (fade-transition 200)
            main-talk
            (fade-transition 200)
            end-clip)
  (define begin-clip (image circ-png #:length 500))
  (define end-clip (image circ-png #:length 500)))

(define (make-talk-video [main-talk : Producer] → Producer)
  ;; defines should be after playlist?
  ;; TODO: allow local defines
  ;; (define begin-clip (image circ-png #:length 500))
  ;; (define end-clip (image circ-png #:length 500))
  (let ([begin-clip (image circ-png #:length 500)]
        [end-clip (image circ-png #:length 500)])
    (playlist begin-clip
              (fade-transition #:length 200)
              main-talk
              (fade-transition #:length 200)
              end-clip)))
(check-type make-talk-video : (→ Producer Producer))

; TODO: add filters
(define (attach-audio [v : Producer][a : Producer][off : Int] → Producer)
  #;(define cleaned-audio
    (attach-filter
     a
     #;(project-filter #:end off)
     #;(envelope-filter 50 #:direction 'in)
     #;(envelope-filter 50 #:direction 'out)))
  (let ([cleaned-audio (attach-filter a)])
    (multitrack v cleaned-audio #:length (get-property v "length" 'int))))
(check-type attach-audio : (→ Producer Producer Int Producer))

;; TODO: use define*
(define (make-conf-talk
         [sp : Producer][sl : Producer][a : Producer][off : Int] → Producer)
  ;; (define X (make-speaker-slides-composite sp sl))
  ;; (define Y (make-talk-video X))
  ;; (define v (make-talk-video Y))
  (let* ([X (make-speaker-slides-composite sp sl)]
         [Y (make-talk-video X)]
         [v (make-talk-video Y)])
    (attach-audio v a off)))
(check-type make-conf-talk : (→ Producer Producer Producer Int Producer))

(check-type (make-conf-talk (blank 100) (blank 100) (blank 100) 0) : Producer)
