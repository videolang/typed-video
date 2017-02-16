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

;; same lengths
(define (f5 {n} [p : (Producer n)] [q : (Producer n)] -> (Producer n))
  (multitrack p q))
(check-type (f5 (blank 10) (blank 10)) : (Producer 10))
(check-type (f5 (blank 10) (blank 20)) : (Producer 10)) ; longer ok
(typecheck-fail (f5 (blank 10) (blank 9)) ; shorter bad
 #:with-msg "expected \\(Producer 10\\), given \\(Producer 9\\)")

;; cant do this yet
#;(define (f6 [n : Int] [p : (Producer n)] -> (Producer n))
  p)
