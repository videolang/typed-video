#lang typed/video
(require turnstile/rackunit-typechecking)

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

(define (f3 [n3 : Int] [p3 : (Producer n3)] -> (Producer n3)) p3)
(check-type (f3 11 (blank 11)) : (Producer 11))

(define (f4 [n4 : Int] [p4 : (Producer n4)] -> (Producer (+ n4 n4)))
  (playlist p4 p4))
(check-type (f4 10 (blank 10)) : (Producer 20))

(define (f5 {n5a} [n5b : Int] [p5 : (Producer n5a)] -> (Producer n5b))
  (cut-producer p5 #:end n5b))

(check-type (f5 3 (blank 10)) : (Producer 3))
(typecheck-fail
 (f5 11 (blank 10))
 #:with-msg
 (add-escs
  "#%app: while applying fn f5;\nfailed condition: (>= n5a n5b);\ninferred: n5a = 10;\nfor function type: (→ #:bind (n5a) (n5b : Int) (p5 : (Producer n5a)) (Producer n5b) #:when (and (>= n5a n5b) (>= n5b 0) (>= n5a 0)))"))

(typecheck-fail
 (f5 -1 (blank 10))
 #:with-msg
 (add-escs
  "#%app: while applying fn f5;\nfailed condition: (>= n5b 0);\ninferred: n5a = 10;\nfor function type: (→ #:bind (n5a) (n5b : Int) (p5 : (Producer n5a)) (Producer n5b) #:when (and (>= n5a n5b) (>= n5b 0) (>= n5a 0)))"))

(define (f6 {n6a} [n6b : Int] [n6c : Int] [p5 : (Producer n6a)]
            -> (Producer (+ n6b n6c)))
  (cut-producer p5 #:end (+ n6b n6c)))

(check-type (f6 3 4 (blank 10)) : (Producer 7))
(typecheck-fail
 (f6 3 8 (blank 10))
 #:with-msg
 (add-escs
  "#%app: while applying fn f6;\nfailed condition: (>= n6a (+ n6b n6c));\ninferred: n6a = 10;\nfor function type: (→ #:bind (n6a) (n6b : Int) (n6c : Int) (p5 : (Producer n6a)) (Producer (+ n6b n6c)) #:when (and (>= n6a (+ n6b n6c)) (>= (+ n6b n6c) 0) (>= n6a 0)))"))
(check-type (f6 -1 8 (blank 10)) : (Producer 7)) ; neg ok
(check-type (f6 8 -1 (blank 10)) : (Producer 7)) ; neg ok

(define (f7 {n7a} [n7b : Int] [p7 : (Producer n7a)] -> (Producer (+ n7a n7b)))
  (playlist p7 (cut-producer p7 #:end n7b)))
(check-type (f7 3 (blank 10)) : (Producer 13))
(typecheck-fail
 (f7 11 (blank 10))
 #:with-msg
 (add-escs
  "#%app: while applying fn f7;\nfailed condition: (>= n7a n7b);\ninferred: n7a = 10;\nfor function type: (→ #:bind (n7a) (n7b : Int) (p7 : (Producer n7a)) (Producer (+ n7a n7b)) #:when (and (>= n7a n7b) (>= n7b 0) (>= (+ n7a n7b) 0) (>= n7a 0)))"))
