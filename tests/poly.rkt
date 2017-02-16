#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

(define (f {n} [p : (Producer n)] -> (Producer n)) p)
(check-type (f (blank 10)) : (Producer 10))
(check-not-type (f (blank 10)) : (Producer 11))
(check-type (f (blank 11)) : (Producer 11))

;; q ignored
(define (f2 {m n} [p : (Producer m)] [q : (Producer n)] -> (Producer m))
  p)
(check-type (f2 (blank 10) (blank 20)) : (Producer 10))
(check-type (f2 (blank 10) (color "green")) : (Producer 10))
(check-type (f2 (color "green") (blank 10)) : Producer)

;; p ignored
(define (f3 {m n} [p : (Producer m)] [q : (Producer n)] -> (Producer n))
  q)
(check-type (f3 (blank 10) (blank 20)) : (Producer 20))
(check-type (f3 (blank 10) (color "green")) : Producer)

;; add lengths
(define (f4 {m n} [p : (Producer m)] [q : (Producer n)] -> (Producer (+ n m)))
  (playlist p q))
(check-type (f4 (blank 10) (blank 20)) : (Producer 30))
(check-type (f4 (color "green") (color "blue")) : Producer)
(check-type (f4 (color "green") (blank 10)) : Producer)
