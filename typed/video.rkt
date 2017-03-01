#lang turnstile
(require (for-syntax "stx-utils.rkt"))
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in video #%app / quotient . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types
 λ #%datum define begin if let let* displayln
 + - min max <= >= < >
 list car cdr null null? hash equal?
 blank color image clip multitrack playlist include-video
 composite-transition fade-transition
 scale-filter attach-filter grayscale-filter cut-producer
 get-property set-property producer-length)
(provide top-level-playlist require-vid
         (rename-out [typed-app #%app]) /
         AnyProducer Producer Transition Filter (for-syntax ~Producer)
         Int Num Bool String Listof Hash Void →
         ann)

;; TODO:
;; - 2017-02-26: λ/video still not working
;; - 2017-02-13: #%module-begin define lifting not working for typed define
;;               DONE 2017-02-24

;; NOTES:
;; if getting "bad syntax" on ids, look for stx+, eg in playlist or multitrack

; ≫ τ ⊢ ⇒ ⇐ ≻ ∀

;; kinds ----------------------------------------------------------------------
(define-syntax-category :: kind)
(define-base-kinds kInt kNat)
(begin-for-syntax
  (define old-kind-rel (current-kindcheck-relation))
  (define (kind-rel k1 k2)
    ;; (printf "k1 = ~a\n" (stx->datum k1))
    ;; (printf "k2 = ~a\n" (stx->datum k2))
    (or (kind=? k1 k2)
        (and (kNat? k1) (kInt? k2))))
  (current-kindcheck-relation kind-rel))

;; types ----------------------------------------------------------------------
(define-base-types String Int Nat Num Bool Hash Void Filter)
(define-type-constructor Listof)
(define-binding-type ∀)
;; TODO: support kws in function type
(define-internal-type-constructor →)
(define-kinded-syntax →
  [(_ #:bind (X ...) ty ...+ #:when C) ≫
   [[X ≫ X- : Int] ... ⊢ [ty ≫ ty- ⇐ #%type] ... [C ≫ C- ⇒ _]]
   ----------
   [≻ #,(add-orig #`(∀ (X- ...) #,(mk-type #'(→- ty- ... C-))) #'(→ ty ...))]]
  [(_ #:bind (X ...) ty ...+) ≫
   ----------
   [≻ (→ #:bind (X ...) ty ... #:when #t)]]
  [(_ ty ...+) ≫
   [⊢ ty ≫ ty- ⇐ #%type] ...
   -----------
   [≻ #,(add-orig #`(∀ () #,(mk-type #'(→- ty- ... #t))) #'(→ ty ...))]])
(define-internal-type-constructor Producer)
;; should use def-kinded-stx but somewhat conflating types and kinds for convenience
#;(define-typed-syntax Producer
  [_:id ≫ ; shorthand for (Producer inf)
   -------------
   [≻ #,(add-orig (mk-type #'(Producer- (v:#%datum . 99999))) #'Producer)]] ; TODO: make this inf?
  [(_ n:exact-nonnegative-integer) ≫ ; calls from impl?
   ----------
   [≻ #,(add-orig (mk-type #'(Producer- n)) #'(Producer n))]]
  [(_ n) ≫ ; calls from user-code
   [⊢ n ≫ n- ⇐ Int] ; must be Int, ow cant do subtraction; TODO: gen constraint
   ----------------
   [≻ #,(add-orig (mk-type #'(Producer- n-)) #'(Producer n))]]
  #;[(_ n)
     #:with n- (expand/df #'n)
     #:when (typecheck? (typeof #'n-) ((current-type-eval) #'Int)) ; any Int *expression* is ok as the type
     (mk-type #'(Producer- n-))]
  [(~and p (_ x)) ≫
   ----------
   [#:error (type-error
             #:src #'p
             #:msg "Producer: expected arg of kind kInt, given ~a" #'x)]])
;; using def-typed-stx for some reason messed up
;; displaying (orig of) failed constraints in #%app ("n" instead of "n2")
;; - not sure where the n even comes from since no examples in the tests use "n"
;; using just def-stx fixes the problem even though the 2 defs look equal
(define-syntax (Producer stx)
  (syntax-parse stx
  [_:id ; shorthand for (Producer inf)
   (add-orig (mk-type #'(Producer- (v:#%datum . 99999))) #'Producer)]
  [(_ n:exact-nonnegative-integer)
   (add-orig (mk-type #'(Producer- n)) #'(Producer n))]
  [(_ n)
   #:with n- (expand/df #'n)
   #:when (typecheck? (typeof #'n-) ((current-type-eval) #'Int))
   ;; #:with n- (expand/df #'n)
   ;;#:when (typecheck? (typeof #'n-) ((current-type-eval) #'Int)) ; any Int *expression* is ok as the type
   (add-orig (mk-type #'(Producer- n-)) #'(Producer n))]
  [(_ x) (type-error
      #:src stx
      #:msg "Producer: expected arg of kind kInt, given ~a" #'x)]))
(define-internal-type-constructor Transition)
(define-syntax (Transition stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Transition- (v:#%datum . 0))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Transition- n)) stx)]))

;; override typecheck-relation to consider numbers and other terms
(begin-for-syntax
  (define old-type? (current-type?))
  (define (new-type? t)
    (or (old-type? t) (Int-ty? (kindof t))))
  (current-type? new-type?)
  
  ;; these preds assume expanded tys
  ;; - lowercase matches literals only, ie singletons
  ;; - uppercase includes general tys, eg Int, Nat, etc
  (define nat-ty?
    (syntax-parser
      [(~or n:exact-nonnegative-integer ; this is from impl code?
            ((~literal quote) n:exact-nonnegative-integer)) ; this is from user code?
       #t]
       [_ #f]))
  (define int-ty?
    (syntax-parser [(~or n:integer ((~literal quote) n:integer)) #t][_ #f]))
  (define num-ty? int-ty?)
  (define (Nat-ty? t) (or (Nat? t) (nat-ty? t)))
  (define (Int-ty? t) (or (Nat? t) (Int? t) (int-ty? t)))
  
  ;; new type relation: a subtyping relation
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    ;; (printf "t1 = ~a\n" (stx->datum t1))
    ;; (printf "t2 = ~a\n" (stx->datum t2))
    (or
     (type=? t1 t2)
     (and (Int-ty? t1) (Num? t2))
     (and (Int-ty? t1) (Int? t2))
     (and (Nat-ty? t1) (Nat? t2))
     (syntax-parse (list t1 t2)
      [((~Listof x) (~Listof y))         (typecheck? #'x #'y)]
      [((~Producer m) (~Producer n))     (typecheck? #'m #'n)]
      [((~Transition m) (~Transition n)) (typecheck? #'m #'n)]
      [((~∀ Xs t1) (~∀ Ys t2))
        (and (stx-length=? #'Xs #'Ys)
             (typecheck? (substs #'Ys #'Xs #'t1) #'t2))]
      [((~→ i ... o c) (~→ j ... p d)) (typechecks? #'(j ... o c) #'(i ... p d))]
      [(((~literal quote) m:number) ((~literal quote) n:number))
       (>= (stx-e #'m) (stx-e #'n))]   ; longer vid is "more precise"
      [(((~literal quote) b1:boolean) ((~literal quote) b2:boolean))
       (equal? (stx-e #'b1) (stx-e #'b2))]
      [(_ ((~literal quote) n:number)) ; AnyProducer needs this
       #:when (zero? (stx-e #'n))
       #t]
      ;; arith expr: sort + terms
      [(((~literal #%plain-app) (~literal v:+) . xs)
        ((~literal #%plain-app) (~literal v:+) . ys))
       (and (stx-length=? #'xs #'ys)
            (typechecks? (stx-sort #'xs) (stx-sort #'ys)))]
      ;; arith expr: others
      [(((~literal #%plain-app)
         (~and op1 (~or (~literal v:>=) (~literal v:quotient) (~literal v:-))) . xs)
        ((~literal #%plain-app)
         (~and op2 (~or (~literal v:>=) (~literal v:quotient) (~literal v:-))) . ys))
       (and (free-id=? #'op1 #'op2)
            (stx-length=? #'xs #'ys)
            (typechecks? #'xs #'ys))]
      [_ #f])))
  (current-typecheck-relation new-type-rel)
  
  ;; new type eval
  (define (lit-stx? x) (define y (stx-e x)) (or (string? y)))
  (define old-eval (current-type-eval))
  (define (new-eval t)
    (syntax-parse (old-eval t)
;      [t+ #:do [(printf "EVALing: ~a\n" (stx->datum #'t+))] #:when #f #'(void)]
      ;; number literals
      [((~literal quote) n:exact-nonnegative-integer) (assign-kind #'n #'Nat)]
      [((~literal quote) s:str) #'s]
      [((~literal quote) b:boolean) #'b]
      ;; if
      #;[(~and orig ((~literal v:if) tst e1 e2))
       #:do [(define res ((current-type-eval) #'tst))]
       (if (boolean? res)
           (if res ((current-type-eval) #'e1)  ((current-type-eval) #'e2))
           #'orig)]
      ;; #%app producer-length
      [((~literal #%plain-app) _ p)
       #:with (~literal v:producer-length) (syntax-property this-syntax 'orig-app)
       #:with (~Producer n) (typeof #'p)
       #'n]
      ;; #%app get-property
      #;[(~and orig ((~literal #%plain-app) _ p k))
       #:with (~literal v:get-property) (syntax-property this-syntax 'orig-app)
       #:do [(define k* (stx-e ((current-type-eval) #'k)))]
       #:when (string? k*)
       #:do [(define v (syntax-property #'p (string->symbol k*)))]
       (or v #'orig)]
      ;; #%app equal?
      #;[(~and orig ((~literal #%plain-app) (~literal v:equal?) e1 e2))
       #:with e1+ ((current-type-eval) #'e1)
       #:with e2+ ((current-type-eval) #'e2)
       (if (and (lit-stx? #'e1+) (lit-stx? #'e2+))
           (equal? (stx-e #'e1+) (stx-e #'e2+))
           #'orig)]
      ;; #%app >=
      [((~literal #%plain-app) (~literal v:>=) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                         ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (stx>= #'ns)]
      ;; #%app +
      #;[((~literal #%plain-app) (~literal v:+) . args)
       #:with ((~or n:integer
                    ((~literal quote) m:integer)
                    other) ...) ; collect unsolved terms
       (stx-map (current-type-eval) #'args)
       (if (stx-null? (attribute other))
           (+ (stx+ #'(n ...)) (stx+ #'(m ...)))
           #`(#%plain-app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...))]
      ;; #%app -
      #;[((~literal #%plain-app) (~literal v:-) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (stx- #'ns)]
      ;; #%app /
      [((~literal #%plain-app) (~literal v:quotient) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (stx/ #'ns)]
      ;; #%app min
      [((~literal #%plain-app) (~literal v:min) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (stx-min #'ns)]
      [(~Producer n)
       ;; TODO: just return inf if cant eval complicated arith expr
       ;; #:do [(printf "Producer with: ~a\n" (stx->datum #'n))
       ;;       (displayln (get-orig this-syntax))]
       #:with n- ((current-type-eval) #'n)
       #:with out-n (if (number? (stx-e #'n-)) #'(#%datum . n-) #'n-)
       (add-orig
        (mk-type (expand/df #'(Producer- out-n)))
        #'(Producer n-))]
      [t+ #'t+]))
  (current-type-eval new-eval)

  (define (lookup Xs X+tys)
    (stx-map (λ (X) (lookup1 X X+tys)) Xs))
  (define (lookup1 Y X+tys)
    (and (not (stx-null? X+tys))
         (syntax-parse (stx-car X+tys)
           [(X ty) #:when (free-id=? Y #'X) #'ty]
           [_ (lookup1 Y (stx-cdr X+tys))])))
      
  (define (unify tysX tys)
    (stx-appendmap unify1 tysX tys))
  (define (unify1 tyX ty)
    (syntax-parse (list tyX ty)
      [((~Producer n) (~Producer m))
       #'((n m))]
      [_ '()]))

  (define current-Cs (make-parameter '()))
  )

(define-syntax define-named-type-alias
  (syntax-parser
    [(_ Name:id τ:any-type)
     #'(define-syntax Name
         (make-variable-like-transformer (add-orig #'τ #'Name)))]
    [(_ (f:id x:id ...) ty) ; dont expand yet
     #'(define-syntax (f stx)
         (syntax-parse stx
           [(_ x ...) (add-orig #'ty stx)]))]))

(define-named-type-alias AnyProducer (Producer 0))

;; prims ----------------------------------------------------------------------

(define-typed-syntax (displayln e) ≫
  [⊢ e ≫ e- ⇒ _]
  ---------
  [⊢ (v:#%app v:displayln e-) ⇒ Void])

(define-typed-syntax min
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:min ⇒ (→ Int Int Int)]]
  [(_ e ...) ≫
   #:with (e* ...)
          (remove-duplicates
           (attribute e)
           (λ (x y) (or (and (id? x) (id? y) (free-id=? x y))
                        (equal? x y))))
   [⊢ e* ≫ e- ⇐ Int] ...
   ----------
   [⊢ #,(if (= 1 (length (attribute e-)))
            (stx-car (attribute e-))
            #'(v:#%app v:min e- ...)) ⇒ Int]])

(define-typed-syntax max
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:max ⇒ (→ Int Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:max e- ...) ⇒ Int]])

(define-typed-syntax +
  #;[_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  #;[((~literal #%plain-app) (~literal v:+) . args)
       #:with ((~or n:integer
                    ((~literal quote) m:integer)
                    other) ...) ; collect unsolved terms
       (stx-map (current-type-eval) #'args)
       (if (stx-null? (attribute other))
           (+ (stx+ #'(n ...)) (stx+ #'(m ...)))
           #`(#%plain-app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...))]
  ;; TODO: remove dup code between Nat and Int
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Nat] ...
   #:with ((~or n:exact-nonnegative-integer
                ((~literal quote) m:exact-nonnegative-integer)
                other)
           ...)
           (stx-map (current-type-eval) #'(e- ...)) ;; TODO: remove type-ev; expanding should be enough?
   ;; #:do[(displayln #'(m ...))
   ;;      (displayln #'(other ...))]
   #:with res (if (stx-null? (attribute other))
                  #`#,(+ (stx+ #'(n ...)) (stx+ #'(m ...)))
                  #`(v:#%app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...))
;   #:do[(displayln #'res)]
   ----------
   [⊢ res #;(v:#%app v:+ 'res other ...) ⇒ Nat]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   #:with ((~or n:integer
                ((~literal quote) m:integer)
                other)
           ...)
           (stx-map (current-type-eval) #'(e- ...)) ;; TODO: remove type-ev; expanding should be enough?
   #:with res (if (stx-null? (attribute other))
                  #`#,(+ (stx+ #'(n ...)) (stx+ #'(m ...)))
                  #`(v:#%app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...))
   ----------
   [⊢ res #;(v:#%app v:+ 'res other ...) ⇒ Int]]
  #;[(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   #:do[(printf "e-: ~a\n" #'(e- ...))]
   #:with ((~or n:integer ((~literal quote) m:integer) other) ...) (stx-map (current-type-eval) #'(e- ...))
   #:do[(printf "m: ~a\n" #'(m ...))]
   #:with res (if (stx-null? (attribute other))
                  #`'#,(stx+ #'(m ...))
                  #`(v:#%app v:+ '#,(stx+ #'(m ...)) other ...))
   #:do[(displayln #'res)]
   ----------
   [⊢ res #;(v:#%app v:+ 'res other ...) ⇒ Int]]
  #;  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ Nat]])

(define-typed-syntax -
  #;[_:id ≫ ; HO use is binary
   ----------
   [⊢ v:- ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   #:with ((~or n:integer
                ((~literal quote) m:integer)
                other)
           ...)
           (stx-map (current-type-eval) #'(e- ...)) ;; TODO: remove type-ev; expanding should be enough?
   #:with res (if (stx-null? (attribute other))
                  #`#,(+ (stx- #'(n ...)) (stx- #'(m ...)))
                  #`(v:#%app v:+ #,(+ (stx- #'(n ...)) (stx- #'(m ...))) other ...))
   ----------
   [⊢ res #;(v:#%app v:+ 'res other ...) ⇒ Int]]
  #;[(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:- e- ...) ⇒ Int]])

;; integer divide
(define-typed-syntax /
  #;[_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Nat] ...
   ----------
   [⊢ (v:#%app v:quotient e- ...) ⇒ Nat]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:quotient e- ...) ⇒ Int]])

(define-typed-syntax equal?
  [(_ e1 e2) ≫
   #;[(~and orig ((~literal #%plain-app) (~literal v:equal?) e1 e2))
       #:with e1+ ((current-type-eval) #'e1)
       #:with e2+ ((current-type-eval) #'e2)
       (if (and (lit-stx? #'e1+) (lit-stx? #'e2+))
           (equal? (stx-e #'e1+) (stx-e #'e2+))
           #'orig)]
   [⊢ e1 ≫ e1- ⇒ _] [⊢ e2 ≫ e2- ⇒ _]
   #:with e1+ ((current-type-eval) #'e1-)
   #:with e2+ ((current-type-eval) #'e2-)
   #:with res (if (and (lit-stx? #'e1+) (lit-stx? #'e2+))
                  #`#,(equal? (stx-e #'e1+) (stx-e #'e2+))
                  #'(v:#%app v:equal? e1- e2-))
   ----------
   [⊢ res #;(v:#%app v:equal? e1- e2-) ⇒ Bool]])

(define-typed-syntax >=
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:>= ⇒ (→ Int Int Bool)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:>= e- ...) ⇒ Bool]])

(define-typed-syntax <=
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:<= ⇒ (→ Int Int Bool)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:<= e- ...) ⇒ Bool]])

(define-typed-syntax >
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:> ⇒ (→ Int Int Bool)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:> e- ...) ⇒ Bool]])

(define-typed-syntax <
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:< ⇒ (→ Int Int Bool)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:< e- ...) ⇒ Bool]])

;; list and hash --------------------------------------------------------------
(define-typed-syntax null
  [(_ ~! τi:type-ann) ≫
   --------
   [⊢ v:null ⇒ (Listof τi.norm)]]
  ; minimal type inference
  [_:id ⇐ (~Listof τ) ≫
   --------
   [⊢ v:null]])
(define-typed-syntax (cons e1 e2) ≫
  [⊢ e1 ≫ e1- ⇒ τ1]
  [⊢ e2 ≫ e2- ⇐ (Listof τ1)]
  --------
  [⊢ (v:#%app v:cons e1- e2-) ⇒ (Listof τ1)])
(define-typed-syntax (null? e) ≫
  [⊢ e ≫ e- ⇒ (~Listof _)]
  --------
  [⊢ (V:#%app v:null? e-) ⇒ Bool])
(define-typed-syntax (car e) ≫
  [⊢ e ≫ e- ⇒ (~Listof τ)]
  --------
  [⊢ (v:#%app v:car e-) ⇒ τ])
(define-typed-syntax (cdr e) ≫
  [⊢ e ≫ e- ⇒ τ-lst]
  #:fail-unless (Listof? #'τ-lst)
  (format "Expected a list type, got: ~a" (type->str #'τ-lst))
  --------
  [⊢ (v:#%app v:cdr e-) ⇒ τ-lst])
(define-typed-syntax list
  [(_) ≫ --- [≻ null]]
  [(_ x . rst) ⇐ (~Listof τ) ≫ ; has expected type
   --------
   [⊢ (cons (add-expected x τ) (list . rst))]]
  [(_ x . rst) ≫ ; no expected type
   --------
   [≻ (cons x (list . rst))]])
(define-typed-syntax hash
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ _] ... ; TODO: dont care for now
   --------
   [⊢ (v:#%app v:hash e- ...) ⇒ Hash]])

;; Racket core forms ----------------------------------------------------------

;; #%datum macro for both types and terms
(define-typed-syntax #%datum
  [(_ . n:exact-nonnegative-integer) ≫ ; use singleton types
   --------
   [⊢ (v:#%datum . n) ⇒ #,(add-orig (assign-kind #'(v:#%datum . n) #'kNat) #'n)
                      #;(⇒ :: #'Nat)]]
  [(_ . n:integer) ≫ ; use singleton types
   --------
   [⊢ (v:#%datum . n) ⇒ #,(add-orig (assign-kind #'(v:#%datum . n) #'kInt) #'n)
                      #;(⇒ :: #'Int)]]
  [(_ . n:number) ≫
   --------
   [⊢ (v:#%datum . n) ⇒ Num]]
  [(_ . s:str) ≫
   ---------
   [⊢ (v:#%datum . s) ⇒ String]]
  [(_ . b:boolean) ≫
   ---------
   [⊢ (v:#%datum . b) ⇒ Bool]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])

;; top-level define
(begin-for-syntax
  (define (transfer-prop p from to)
    (define v (syntax-property from p))
    (syntax-property to p v))
  (define (transfer-props from to)
    (define props (syntax-property-symbol-keys from))
    (define props/filtered (remove 'origin (remove 'orig (remove ': props))))
    (foldl (lambda (p stx) (transfer-prop p from stx)) 
           to 
           props/filtered)))

;; TODO: internal defines
(define-typed-syntax define
  ;; define for values --------------------
  [(_ x:id (~datum :) τ:type e:expr) ≫
   ;[⊢ e ≫ e- ⇐ τ.norm] ; ok? since it gets lifted to top?
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer (⊢ y : τ.norm)))
        (define- y (ann e : τ.norm)))]]
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ] ; gets lifted to top? works with mutual refers?
   #:with y (generate-temporary #'x)
   #:with y+props (transfer-props #'e- (assign-type #'y #'τ))
   --------
   [≻ (begin-
        (define-syntax x (make-rename-transformer #'y+props))
        (define- y e-))]]
  ;; define for functions --------------------
  ;; polymorphic: explicit forall, TODO: infer tyvars
  [(_ (f Xs [x (~datum :) ty] ... (~optional (~seq #:when C) #:defaults ([C #'#t]))
            (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:when (brace? #'Xs)
   #:with ty-expected #'(→ #:bind Xs ty ... ty_out #:when C)
   ;; expanding the λ here means mutual recursion wont work
   ;; but need to to get back τ_f, which may contain new constraints
   ;; (when compared to ty-expected)
   [⊢ (add-expected (λ (x ...) (begin e ...)) ty-expected) ≫ lam- ⇒ τ_f]
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f (make-rename-transformer (⊢ f- : τ_f)))
        (define- f- lam-))]]
  ;; monomorphic case, mutual recursion works ok
  [(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
        (define- f-
          (λ ([x : ty] ...)
            (ann (begin e ...) : ty_out))))]])

(define-typed-syntax λ #:datum-literals (:)
  [(_ (x:id ...) e) ≫
   #:with expected-ty (get-expected-type this-syntax)
   #:when (syntax-e #'expected-ty)
   #:with (~∀ (X ...) (~→ τ_in ... τ_out C0)) #'expected-ty
   #:do[(current-Cs '())] ; reset Cs; this is essentially parameterize
   [([X ≫ X- : Int] ...) ([x ≫ x- : τ_in] ...) ⊢ e ≫ e- ⇐ τ_out]
   #:with C (if (null? (current-Cs)) #'C0
                ;; TODO: update orig: replace with X ...
                (car (map (λ (C) (substs #'(X ...) #'(X- ...) (syntax-local-introduce C))) (current-Cs))))
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ #:bind (X ...) τ_in ... τ_out #:when C)]] ; TODO: should be (and C0 C)?
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  #;[(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out _) ≫ ; TODO: add forall? I think this is covered by 1st case and can be deleted
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (v:λ (x- ...) e-)]])

(define-typed-syntax typed-app
  [(_ e_fn e_arg ...) ≫ ;; must instantiate
   [⊢ e_fn ≫ e_fn- ⇒ (~and ty-orig (~∀ (X ...+) ~! (~→ τ_inX ... τ_outX CX)))]
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ _ ⇒ τ_arg] ...
   #:with (X+ty ...) (unify #'(τ_inX ...) #'(τ_arg ...))
   #:with solved-tys (lookup #'(X ...) #'(X+ty ...))
   #:with (τ_in ... τ_out C)
          (substs #'solved-tys
                  #'(X ...)
                  #'(τ_inX ... τ_outX CX))
   #:with C- ((current-type-eval) #'C)
   #:fail-unless (stx-e #'C-) (format "failed condition: ~a; inferred: ~a\n"
                                      (type->str #'CX)
                                      (string-join
                                       (map (λ (X ty)
                                              (syntax-parse ty
                                                [(_ n)
                                                 (string-append (type->str X) " = "
                                                                (number->string (stx->datum #'n)))]))
                                           (stx->list #'(X ...))
                                           (stx->list #'solved-tys))
                                       ","))
   #:do [(unless (or (boolean? (stx-e #'C-)) (boolean? (stx-e (stx-cadr #'C-))))
           ;; update C's orig with instantiation
           (define old-orig (get-orig #'C))
           (define new-orig
             (substs #'solved-tys #'(X ...) old-orig stx-datum=?))
           (define C-with-new-orig
             (syntax-property #'C 'orig (list new-orig)))
           (current-Cs (cons C-with-new-orig (current-Cs))))]
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ... ; double expand?
   --------
   [⊢ (v:#%app e_fn- e_arg- ...) ⇒ τ_out]]
  [(_ e_fn e_arg ...) ≫ ;; non-polymorphic
   [⊢ e_fn ≫ e_fn- ⇒ (~∀ () ~! (~→ τ_in ... τ_out _))]
   #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
   --------
   [⊢ (v:#%app e_fn- e_arg- ...) ⇒ τ_out]])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

(define-typed-syntax begin
  [(_ e_unit ... e) ⇐ τ_expected ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇐ τ_expected]
   --------
   [⊢ (v:begin e_unit- ... e-)]]
  [(_ e_unit ... e) ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇒ τ_e]
   --------
   [⊢ (v:begin e_unit- ... e-) ⇒ τ_e]])

(begin-for-syntax 
  (define current-join 
    (make-parameter 
      (λ (x y) 
        (unless (typecheck? x y)
          (type-error
            #:src x
            #:msg  "branches have incompatible types: ~a and ~a" x y))
        x))))

(define-syntax ⊔
  (syntax-parser
    [(⊔ τ1 τ2 ...)
     (for/fold ([τ ((current-type-eval) #'τ1)])
               ([τ2 (in-list (stx-map (current-type-eval) #'[τ2 ...]))])
       ((current-join) τ τ2))]))

(define-typed-syntax if
  #;[(~and orig ((~literal v:if) tst e1 e2))
       #:do [(define res ((current-type-eval) #'tst))]
       (if (boolean? res)
           (if res ((current-type-eval) #'e1)  ((current-type-eval) #'e2))
           #'orig)]
  [(_ e_tst e1 e2) ⇐ τ-expected ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇐ τ-expected]
   [⊢ e2 ≫ e2- ⇐ τ-expected]
   #:do[(define tst-val ((current-type-eval) #'e_tst-))]
   #:with res (if (boolean? (stx-e tst-val))
                  (if (stx-e tst-val) ((current-type-eval) #'e1-) ((current-type-eval) #'e2-))
                  #'(v:if e_tst- e1- e2-))
   --------
   [⊢ res #;(v:if e_tst- e1- e2-)]]
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   #:do[(define tst-val ((current-type-eval) #'e_tst-))]
   #:with res (if (boolean? (stx-e tst-val))
                  (if (stx-e tst-val) ((current-type-eval) #'e1-) ((current-type-eval) #'e2-))
                  #'(v:if e_tst- e1- e2-))
   #:with res-ty (if (boolean? (stx-e tst-val)) (if (stx-e tst-val) #'τ1 #'τ2) #'(⊔ τ1 τ2))
   --------
   [⊢ res #;(v:if e_tst- e1- e2-) ⇒ res-ty #;(⊔ τ1 τ2)]])

(define-typed-syntax let
  [(_ ([x e] ...) e_body ...) ⇐ τ_expected ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (v:let ([x- e-] ...) e_body-)]]
  [(_ ([x e] ...) e_body ...) ≫
   [⊢ e ≫ e- ⇒ : τ_x] ...
   [[x ≫ x- : τ_x] ... ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (v:let ([x- e-] ...) e_body-) ⇒ τ_body]])

(define-typed-syntax let*
  [(_ () e_body ...) ≫
   --------
   [≻ (begin e_body ...)]]
  [(_ ([x e] [x_rst e_rst] ...) e_body ...) ≫
   --------
   [≻ (let ([x e]) (let* ([x_rst e_rst] ...) e_body ...))]])



;; basic Video producers ------------------------------------------------------
(define-typed-syntax blank
  [(_ n) ≫
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:blank n-) ⇒ (Producer n)]])

;; TODO: abstract definitions of these producers
;; TODO: add HO case
(define-typed-syntax color
  [(_ c) ≫
   [⊢ c ≫ c- ⇐ String]
   --------
   [⊢ (v:#%app v:color c-) ⇒ Producer]]
  [(_ c #:length n) ≫
   [⊢ c ≫ c- ⇐ String]
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:color c- #:length n-) ⇒ (Producer n)]])

(define-typed-syntax image
  [(_ f) ≫
   [⊢ f ≫ f- ⇐ String]
   --------
   [⊢ (v:#%app v:image f-) ⇒ Producer]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:image f- #:length n-) ⇒ (Producer n)]])

(define-typed-syntax clip
  [(_ f:str) ≫ ; literal arg
   [⊢ f ≫ f- ⇐ String]
   #:do [(define len
           (with-handlers ([exn? (λ _ #f)])
             (parameterize ([current-namespace (make-base-namespace)])
               (namespace-require 'video)
               (eval `(get-property
                       (clip ,(syntax->datum #'f))
                       "length" 'int)))))]
   --------
   [⊢ (v:#%app v:clip f-) ⇒ #,(or (and len #`(Producer #,len))
                                  #'Producer)]]
  [(_ f) ≫
   [⊢ f ≫ f- ⇐ String]
   --------
   [⊢ (v:#%app v:clip f-) ⇒ Producer]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:clip f- #:length n-) ⇒ (Producer n)]]
  [(_ f #:properties (~and props ((~literal hash) (~seq k:str v:str) ...))) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ props ≫ props- ⇒ _]
   --------
   [⊢ #,(add-stx-props
         #'(v:#%app v:clip f- #:properties props-)
         #'(k ...) #'(v ...)) ⇒ Producer]]
  [(_ f #:properties props) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ props ≫ props- ⇒ _]
   --------
   [⊢ (v:#%app v:clip f- #:properties props-) ⇒ Producer]]
  [(_ f #:start n #:end m) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Nat]
   [⊢ m ≫ m- ⇐ Nat]
   --------
   [⊢ (v:#%app v:clip f- #:start n- #:end m-) ⇒ (Producer (+ (- m n) 1))]])

(define-typed-syntax (producer-length p) ≫
  [⊢ p ≫ p- ⇒ (~Producer _)]
  ---------
  [⊢ #,(syntax-property
        #'(v:#%app v:producer-length p-)
        'orig-app
        #'v:producer-length) ⇒ Nat])

;; playlist combinators -------------------------------------------------------
;; TODO: should be interleaved Transition and Producer?
(define-typed-syntax multitrack
  [(_ (~and p (~not _:keyword)) ... #:transitions trans #:length n ~!) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)] ...
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   [⊢ n ≫ n- ⇐ Nat]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:transitions trans- #:length n-) ⇒ (Producer n)]]
  [(_ (~and p (~not _:keyword)) ... #:transitions trans ~!) ≫
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:transitions trans-) ⇒ (Producer (min n ...))]]
  [(_ (~and p (~not _:keyword)) ... #:length n ~!) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:when (stx-andmap (λ (t) (or (Transition? t) (Producer? t))) #'(ty ...))
   [⊢ n ≫ n- ⇐ Nat]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:length n-) ⇒ (Producer n)]]
  [(_ p ...) ≫ ; producers only
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ------------
   [⊢ (v:#%app v:multitrack p- ...) ⇒ (Producer (min n ...))]]
  [(_ p/t ...) ≫
;   [⊢ p ≫ p- ⇒ (~or (~Producer n) (~Transition m))] ... ; doesnt work, get #fs on non-match
   [⊢ p/t ≫ p/t- ⇒ ty] ...
   #:with ((~or (~Producer n) (~Transition _)) ...) #'(ty ...)
   ------------
   [⊢ (v:#%app v:multitrack p/t- ...) ⇒ (Producer (min n ...))]])

;; TODO: check interleaving of producers and transitions
;; TODO: check that stitching lengths is ok
;; eg, this is bad (playlist (blank 1) (fade-transition #:len 2) (blank 1))
(define-typed-syntax playlist
  [(_ p ... #:transitions trans) ≫ ; producers + transitions
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ;; TODO: subtract transitions?
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   ------------
   [⊢ (v:#%app v:playlist p- ... #:transitions trans-)
      ⇒ #,(mk-type #`(Producer- #,(stx+ (attribute n))))]]
  [(_ p ...) ≫ ; producers only
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ------------
   [⊢ (v:#%app v:playlist p- ...) ⇒ (Producer (+ n ...))]]
  [(_ p1 p/t ... pn) ≫ ; producers + transitions
   [⊢ p1 ≫ p1- ⇒ (~Producer n1)]
   [⊢ pn ≫ pn- ⇒ (~Producer nn)]
   ;[⊢ p/t ≫ p/t- ⇒ (~or (~Producer n) (~Transition m))] ... ; doesnt work
   [⊢ p/t ≫ p/t- ⇒ P-or-T] ...
   #:with ((~or (~Producer n) (~Transition m)) ...) #'(P-or-T ...)
   ------------
   [⊢ (v:#%app v:playlist p1- p/t- ... pn-) 
      ⇒ (Producer (+ n1 nn n ... (- (+ m ...))))]]
  [xs ≫
   ------------
   [#:error
    (type-error
     #:src #'xs
     #:msg "playlist must interleave producers and transitions, given: ~v"
     #'xs)]])
(define-typed-syntax top-level-playlist
  [(_ p ...) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:with ((p* _) ...) (stx-filter-out-false #'(p ...) #'(ty ...))
   --------
   [≻ (playlist p* ...)]])

;; transitions ----------------------------------------------------------------
(define-typed-syntax composite-transition
  [(_ x y w h) ≫
   [⊢ x ≫ x- ⇐ Num]
   [⊢ y ≫ y- ⇐ Num]
   [⊢ w ≫ w- ⇐ Num]
   [⊢ h ≫ h- ⇐ Num]
   --------
   [⊢ (v:#%app v:composite-transition x- y- w- h-) ⇒ Transition]]
  [(_ x y w h #:top t #:bottom b) ≫
   [⊢ x ≫ x- ⇐ Num]
   [⊢ y ≫ y- ⇐ Num]
   [⊢ w ≫ w- ⇐ Num]
   [⊢ h ≫ h- ⇐ Num]
   [⊢ t ≫ t- ⇐ AnyProducer]
   [⊢ b ≫ b- ⇐ AnyProducer]
   --------
   [⊢ (v:#%app v:composite-transition x- y- w- h- #:top t- #:bottom b-)
      ⇒ Transition]])

(define-typed-syntax fade-transition
  [(_ #:length n:exact-nonnegative-integer) ≫
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:fade-transition #:length n-) ⇒ (Transition n)]]
  [(_ #:length n) ≫
   [⊢ n ≫ n- ⇐ Nat]
   --------
   [⊢ (v:#%app v:fade-transition #:length n-) ⇒ Transition]])

;; filters
(define-typed-syntax scale-filter
  [(_ p w h) ≫
   [⊢ w ≫ w- ⇐ Int]
   [⊢ h ≫ h- ⇐ Int]
   [⊢ p ≫ p- ⇒ (~and ty_out (~Producer _))]
   -----------
   [⊢ (v:#%app v:scale-filter p- w- h-) ⇒ ty_out]])

(define-typed-syntax grayscale-filter
  [(_ p) ≫
   [⊢ p ≫ p- ⇒ (~and ty_out (~Producer _))]
   -----------
   [⊢ (v:#%app v:grayscale-filter p-) ⇒ ty_out]])

(define-typed-syntax attach-filter
  [(_ p f ...) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)]
   [⊢ f ≫ f- ⇐ Filter] ...
   -----------
   [⊢ (v:#%app v:attach-filter p- f- ...) ⇒ Producer]])

(define-typed-syntax cut-producer
  [(_ p #:start m) ≫
   [⊢ p ≫ p- (⇐ (Producer m)) (⇒ (~Producer n))]
   [⊢ m ≫ m- ⇐ Int]
   -----------
   [⊢ (v:#%app v:cut-producer p- #:start m-) ⇒ (Producer (+ 1 (- n m)))]]
  [(_ p #:start m #:end n) ≫
   [⊢ p ≫ _ ⇐ (Producer m)]
   [⊢ p ≫ p- ⇐ (Producer (+ 1 (- n m)))]
   [⊢ m ≫ m- ⇐ Int]
   [⊢ n ≫ n- ⇐ Int]
   -----------
   [⊢ (v:#%app v:cut-producer p- #:start m- #:end n-) ⇒ (Producer (+ 1 (- n m)))]])
   

;; props ----------------------------------------------------------------------
(define-typed-syntax get-property
  [(_ p k) ≫
   [⊢ p ≫ p- ⇐ Producer]
   [⊢ k ≫ k- ⇐ String]
   #:do [(define k* (stx-e ((current-type-eval) #'k-)))]
   #:with res (if (string? k*)
                  (let ([v (syntax-property #'p- (string->symbol k*))])
                    (or #`#,v #'(v:#%app v:get-property p- k-)))
                  #'(v:#%app v:get-property p- k-))
   --------
   [⊢ #,(syntax-property
         #'res
;         #'(v:#%app v:get-property p- k-)
         'orig-app #'v:get-property) ⇒ String]]
  [(_ p k (_ (~datum int))) ≫
   [⊢ p ≫ p- ⇐ Producer]
   [⊢ k ≫ k- ⇐ String]
   --------
   [⊢ (v:#%app v:get-property p- k- 'int) ⇒ Int]]
  [(_ p k (_ (~datum bool))) ≫ ; TODO: a hack, how does this work?
   [⊢ p ≫ p- ⇐ Producer]
   [⊢ k ≫ k- ⇐ String]
   --------
   [⊢ (v:#%app v:get-property p- k-) ⇒ Bool]])

(define-typed-syntax set-property
  [(_ p k v) ≫
   [⊢ p ≫ p- ⇒ (~and ty_out (~Producer _))]
   [⊢ k ≫ k- ⇐ String]
   [⊢ v ≫ v- ⇒ _]
   --------
   [⊢ (v:#%app v:set-property p- k- v-) ⇒ ty_out]])

(define-typed-syntax include-video
  [(_ v #:start m #:end n) ≫
   ;; TODO: check that n-m is an ok length against actualy type
   [⊢ v ≫ v- ⇐ String]
   [⊢ m ≫ m- ⇐ Int]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:include-video v- #:start m- #:end n-)
      ⇒ (Producer (+ 1 (- n m)))]]
  [(_ v) ≫
   [⊢ v ≫ (~and v- (_ v--)) ⇐ String]
   #:with tmp (generate-temporary)
   #:with vid (datum->syntax #'v 'vid)
   #:with vid-ty2 (datum->syntax #'v 'vid-ty2)
   [⊢ (let-syntax- ([tmp (make-variable-like-transformer
                          (syntax-property
                           #'(dynamic-require 'v 'vid)
                           ':
                           (local-expand
                            #`(Producer (#%datum . #,(dynamic-require 'v 'vid-ty2)))
                            'expression null)))])
                   tmp)
      ≫ (_ () (_ () e-)) ⇒ _] ; extract from let-values remnants of let-stx
   --------
   [≻ e-]])

(define-typed-syntax require-vid
  [(_ f)≫
   #:with vid (datum->syntax #'f 'vid)
   #:with v-vid (datum->syntax #'f 'v-vid)
   #:with v-vid-ty (datum->syntax #'f 'v-vid-ty)
   ----------
   [≻ (begin-
        (require- (prefix-in- v- f))
        (define-syntax- vid
          (make-rename-transformer
           (assign-type #'v-vid #'v-vid-ty))))]])
