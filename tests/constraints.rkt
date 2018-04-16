#lang typed/video
(require turnstile/rackunit-typechecking)

;; more constraint testing

;; producer-length
(check-type (producer-length (blank 10)) : 10)
(check-type (producer-length (blank 10)) : Int)

(define bl10 (blank 10))
(check-type bl10 : (Producer 10))
(typecheck-fail (Producer Bool)
                #:with-msg "expected expression of type Int, given Bool")

;; test singleton types
(check-type (blank (producer-length bl10)) : (Producer 10))
(check-type (blank (producer-length bl10)) : (Producer 9)) ; < ok
(check-not-type (blank (producer-length bl10)) : (Producer 11)) ; > not ok
(check-type (blank (+ 2 (producer-length bl10))) : (Producer 12))

(define bl10-len (producer-length bl10))
(check-type (blank bl10-len) : (Producer 10))

(define bl10-len+2 (+ 2 (producer-length bl10)))
(check-type (blank bl10-len+2) : (Producer 12))

(define bl10-len-2 (- (producer-length bl10) 2))
(check-type (blank bl10-len-2) : (Producer 8))

(define bl10-len2 (+ 2 (- (producer-length bl10) 2)))
(check-type (blank bl10-len2) : (Producer 10))

;; fails immediate Producer side-condition check
(typecheck-fail
 (blank -1)
 #:with-msg
 "constraints.rkt.*Producer: expression has type \\(Producer -1\\), which fails side-condition: \\(>= -1 0\\)")
(typecheck-fail (blank (- bl10-len 11))
 #:with-msg
 "constraints.rkt.*Producer: expression has type \\(Producer \\(- bl10-len 11\\)\\), which fails side-condition: \\(>= \\(- bl10-len 11\\) 0\\)")
(check-type (blank (- bl10-len 10)) : (Producer 0))
(check-type (blank (- bl10-len bl10-len)) : (Producer 0))

(check-type (multitrack bl10 #:length (- (producer-length bl10) 1)) : (Producer 9))
(check-type (multitrack bl10 #:length (- (producer-length bl10) 1))
            : (Producer (- (producer-length bl10) 1)))

;; implicit constraint from Producer
(define (f1 {n1} [p1 : (Producer n1)] -> (Producer (- n1 5)))
  (multitrack p1 #:length (- (producer-length p1) 5)))

;; (check-type (f1 (blank 10)) : (Producer 5))
;; fails propagated Producer side-condition check
(typecheck-fail
 (f1 (blank 2))
 #:with-msg
 (add-escs
  "#%app: while applying fn f1;\nfailed condition: (>= (- n1 5) 0);\ninferred: n1 = 2;\nfor function type: (→ #:bind (n1) (p1 : (Producer n1)) (Producer (- n1 5)) #:when (and (>= (- n1 5) 0) (>= n1 0)))\n  at: (#%app f1 (blank 2))"))

;; explicit >= constraint
(define (f2 {n2} [p2 : (Producer n2)] #:when (>= n2 100) -> (Producer n2)) p2)

(check-type (f2 (blank 100)) : (Producer 100))
(typecheck-fail
 (f2 (blank 99))
 #:with-msg
 (add-escs
  "#%app: while applying fn f2;\nfailed condition: (>= n2 100);\ninferred: n2 = 99;\nfor function type: (→ #:bind (n2) (p2 : (Producer n2)) (Producer n2) #:when (and (>= n2 100) (>= n2 0)))"))

;; explicit <= constraint
(define (f3 {n3} [p3 : (Producer n3)] #:when (<= n3 100) -> (Producer n3)) p3)
(check-type (f3 (blank 99)) : (Producer 99))
(typecheck-fail
 (f3 (blank 101))
 #:with-msg
 (add-escs
  "#%app: while applying fn f3;\nfailed condition: (<= n3 100);\ninferred: n3 = 101;\nfor function type: (→ #:bind (n3) (p3 : (Producer n3)) (Producer n3) #:when (and (<= n3 100) (>= n3 0)))"))

;; implicit constraint (from typechecking Producer)
;; - generates constraint n4 >= n4 - 5
;; - a better constraint-solving alg would return true
;;   but our naive alg propagates the constraint for now
(define (f4 {n4} [p4 : (Producer n4)] -> (Producer (- n4 5)))
  (cut-producer p4 #:end (- (producer-length p4) 5)))
(check-type (f4 (blank 10)) : (Producer 5))
(typecheck-fail
 (f4 (blank 3))
 #:with-msg
 (add-escs
"#%app: while applying fn f4;\nfailed condition: (>= (- n4 5) 0);\ninferred: n4 = 3;\nfor function type: (→ #:bind (n4) (p4 : (Producer n4)) (Producer (- n4 5)) #:when (and (>= n4 (- (producer-length p4) 5)) (>= (- n4 5) 0) (>= n4 0)))"))
;; def wont fail bc solving alg cant determine n4 - 6 + 1 >= n4
;; but every app of f4* will fail
(define (f4* {n4} [p4 : (Producer n4)] -> (Producer n4))
  (cut-producer p4 #:end (- (producer-length p4) 5)))
(check-type
 f4* :
 (→ #:bind (n4)
    (p4 : (Producer n4))
    (Producer n4)
    #:when (and (>= (- (producer-length p4) 5) n4)
                (>= n4 (- (producer-length p4) 5))
                (>= (- (producer-length p4) 5) 0)
                (>= n4 0))))
(typecheck-fail
 (f4* (blank 0))
 #:with-msg
 (add-escs
  "#%app: while applying fn f4*;\nfailed condition: (>= (- n4 5) n4);\ninferred: n4 = 0;\nfor function type: (→ #:bind (n4) (p4 : (Producer n4)) (Producer n4) #:when (and (>= (- (producer-length p4) 5) n4) (>= n4 (- (producer-length p4) 5)) (>= (- (producer-length p4) 5) 0) (>= n4 0)))"))
(typecheck-fail
 (f4* (blank 100))
 #:with-msg
 (add-escs
  "#%app: while applying fn f4*;\nfailed condition: (>= (- n4 5) n4);\ninferred: n4 = 100;\nfor function type: (→ #:bind (n4) (p4 : (Producer n4)) (Producer n4) #:when (and (>= (- (producer-length p4) 5) n4) (>= n4 (- (producer-length p4) 5)) (>= (- (producer-length p4) 5) 0) (>= n4 0)))"))
;; explicit + implicit constraint
(define (f5 {n5} [p5 : (Producer n5)] #:when (<= n5 100) -> (Producer (- n5 5)))
  (cut-producer p5 #:end (- (producer-length p5) 5)))
(check-type (f5 (blank 10)) : (Producer 5))
(check-type (f5 (blank 5)) : (Producer 0))
;; f5 fail: too low
(typecheck-fail
 (f5 (blank 3))
 #:with-msg
 (add-escs
  "#%app: while applying fn f5;\nfailed condition: (>= (- n5 5) 0);\ninferred: n5 = 3;\nfor function type: (→ #:bind (n5) (p5 : (Producer n5)) (Producer (- n5 5)) #:when (and (<= n5 100) (>= n5 (- (producer-length p5) 5)) (>= (- n5 5) 0) (>= n5 0)))"))
(typecheck-fail
 (f5 (blank 4))
 #:with-msg
 (add-escs
  "#%app: while applying fn f5;\nfailed condition: (>= (- n5 5) 0);\ninferred: n5 = 4;\nfor function type: (→ #:bind (n5) (p5 : (Producer n5)) (Producer (- n5 5)) #:when (and (<= n5 100) (>= n5 (- (producer-length p5) 5)) (>= (- n5 5) 0) (>= n5 0)))"))
;; f5 fail: too high

;; no failing cases?
(define (f6 {n6} [p6 : (Producer (- n6 1))] -> (Producer n6))
  (playlist (blank 1) p6))
(check-type (f6 (blank 0)) : (Producer 1))
(check-type (f6 (blank 100)) : (Producer 101))
