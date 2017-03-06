#lang typed/video
(require turnstile/examples/tests/rackunit-typechecking)

;; more dependent type tests

(define (f1 {} [n1 : Int] [p1 : (Producer n1)] -> (Producer n1))
  p1)

(check-type (f1 1 (blank 10)) : (Producer 1)) ; longer ok
(check-type (f1 10 (blank 10)) : (Producer 10))
(typecheck-fail (f1 10 (blank 9))
                #:with-msg
                (add-escs "type mismatch: expected (Producer 10), given (Producer 9)"))
(typecheck-fail/toplvl
 (define (f2 {} [n2 : Bool] [p2 : (Producer n2)] -> (Producer n2)) p2)
 #:with-msg "Producer: expected expression of type Int, given n2 with type Bool")
