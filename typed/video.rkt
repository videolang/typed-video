#lang turnstile
(require (for-syntax "stx-utils.rkt"))
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in
                   video
                   #%app / quotient producer-length ; manually provided
                   . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types
 λ #%datum define begin if let let* displayln
 + - min max <= >= < >
 list car cdr null null? hash equal? and
 blank color image clip multitrack playlist include-video
 composite-transition fade-transition
 scale-filter attach-filter grayscale-filter cut-producer
 get-property set-property #;producer-length)
(provide top-level-playlist require-vid #%type
         (rename-out [typed-app #%app]) /
         AnyProducer Producer Transition Filter (for-syntax ~Producer)
         Int Nat Num Bool String Listof Hash Void →
         ann)

;; TODO:
;; - 2017-02-26: λ/video still not working
;; - 2017-02-13: #%module-begin define lifting not working for typed define
;;               DONE 2017-02-24
;; - 2017-03-03: most Nats (eg, for #:length args) should be Ints
;; - 2017-03-03: change #:end's to be exclusive
;; - 2017-03-03: use actual +inf.0 instead of 99999

;; debugging NOTES:
;; 1) err: "bad syntax" on ids: look for stx+, eg in playlist or multitrack
;; 2) err: "expected Int": check type-eval for that case calls mk-type/Int
;; 3) err: "expected stx": check type-eval returns stx or that case

; ≫ τ ⊢ ⇒ ⇐ ≻ ∀ → (fn)

;; kinds ----------------------------------------------------------------------
(define-syntax-category :: kind)
(begin-for-syntax
  ;; ;; new kind relation: a subtyping relation that allows Int and Nat as
  ;; ;; subtypes of #%type
  ;; (define old-kind-rel (current-kindcheck-relation))
  ;; (define (new-kind-rel k1 k2)
  ;;   (printf "k1 = ~a\n" (stx->datum k1))
  ;;   (printf "k2 = ~a\n" (stx->datum k2))
  ;;   (old-kind-rel k1 k2))
  ;; (current-kindcheck-relation new-kind-rel)
  )
  
;; types ----------------------------------------------------------------------
(define-base-types String Int Nat Num Bool Hash Void Filter)
(begin-for-syntax
  (define Int+ (expand/df #'Int))
  (define (typecheck/Int? t) (typecheck? t Int+))
  (define (mk-type/Int t) (assign-type t Int+))
  
  (define (is-type? t)
    (or (#%type? (kindof t)) (arith-type? t)))
  (current-type? is-type?)

  ;; handle arith exprs used as types
  (define (arith-type? t)
    (define ty-as-k (typeof t))
    (and ty-as-k
         (or
          ;; this case handles when arith expr is lifted to type
          (typecheck/Int? ty-as-k)
          ;; this case handles when arith expr is written directly as type
          (let ([ty-as-kk (typeof ty-as-k)])
            (and ty-as-kk (typecheck/Int? ty-as-kk)))))))

(define-type-constructor Listof)
(define-binding-type ∀)
;; TODO: support kws in function type
(define-internal-type-constructor →)
(define-kinded-syntax →
  [(_ #:bind (X ...) ty ...+ #:when C ~!) ≫
   [[X ≫ X- : Int] ... ⊢ [ty ≫ ty- ⇒ _] ... [C ≫ C- ⇒ : ~Bool]]
   #:when (stx-andmap (λ (t) (or ((current-type?) t)
                                 (type-error #:src t #:msg "given invalid type: ~a\n" t)))
                      #'(ty- ...))
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
(define-syntax (Producer stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     ; TODO: this should use +inf.0 but using an int makes things easier for now
     (add-orig (mk-type #'(Producer- (v:#%datum . 999999))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Producer- n)) stx)]
    [(_ n) ; must accept Ints (as opposed to restricting to Nats), for -, etc
     #:with n- (pass-orig ((current-type-eval) #'n) #'n)
     ;; #:do[(printf "n-: ~a\n" (stx->datum #'n-))
     ;;      (printf "n- ty: ~a\n" (typeof #'n-))]
     ;; check type
     #:when (arith-type? #'n-) ; any Int arith expr arg is ok
     ;; commit to this clause, then check or propagate constraint
     #:with (~and ~! C-) ((current-type-eval) #'(v:#%app v:>= n- 0))
     ;; #:do[(printf "C-: ~a\n" (stx->datum #'C-))
     ;;      (printf "want orig: ~a\n" (stx->datum #`(>= #,(get-orig #'n-) 0)))]
     #:fail-unless (stx-e #'C-)
                   (fmt "expression has type ~a, which fails side-condition: ~a"
                        (stx->datum this-syntax) (stx->datum #'(>= n 0)))
     ;; - Producer must propagate constraint bc instatiation wont expand surface-lvl
     ;; Producer, ie arg wont be re-checked to satisfy >= 0
     ;; - n- and C- must go through the same expansion, but type-eval also expands
     ;; so be careful here
     #:do [(unless (or (boolean? (stx-e #'C-)) (boolean? (stx-e (stx-cadr #'C-))))
             (current-Cs (cons (add-orig #'(v:#%app v:>= n- 0) #`(>= #,(get-orig #'n-) 0))
                               (current-Cs))))]
     (add-orig (mk-type #'(Producer- n-)) stx)]
    [(_ x) (type-error
            #:src stx
            #:msg "Producer: expected expression of type Int, given ~a with type ~a"
            #'x #`#,(typeof ((current-type-eval) #'x)))]))
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
  ;(define num-ty? int-ty?)
  (define (Nat-ty? t) (or (Nat? t) (nat-ty? t)))
  (define (Int-ty? t) (or (Nat? t) (Int? t) (int-ty? t) (arith-type? t)))
  
  ;; new type relation: a subtyping relation
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    ;; (printf "t1 = ~a\n" (stx->datum t1))
    ;; (printf "t2 = ~a\n" (stx->datum t2))
    ;; (printf "t1* = ~a\n" (stx->datum ((current-type-eval) t1)))
    ;; (printf "t2* = ~a\n" (stx->datum ((current-type-eval) t2)))
    (and t1 t2 ; #f possible bc tys may have "type" (:) *or* kind #%type (::)
    (or
     ((current-type=?) t1 t2)
     (equal? (stx-e t1) (stx-e t2)) ; singleton types
     (and (Int-ty? t1) (Num? t2))
     (and (Int-ty? t1) (Int? t2))
     (and (Nat-ty? t1) (Nat? t2))
     (syntax-parse (list t1 t2)
      [(((~literal #%expression) e) _) (typecheck? #'e t2)] ; and generates these?
      [(_ ((~literal #%expression) e)) (typecheck? t1 #'e)] ; and generates these?
      [((~Listof x) (~Listof y))         (typecheck? #'x #'y)]
      [((~Producer m) (~Producer n))     (typecheck? #'m #'n)]
      [((~Transition m) (~Transition n)) (typecheck? #'m #'n)]
      [((~∀ Xs t1) (~∀ Ys t2))
        (and (stx-length=? #'Xs #'Ys)
             (typecheck? (substs #'Ys #'Xs #'t1) #'t2))]
      ;; TODO: enable checking of constraints in fns
      [((~→ i ... o c) (~→ j ... p d)) (typechecks? #'(j ... o) #'(i ... p))]
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
      ;; 2 Int exprs, not stx=?, so generate constraint
      [_ #:when (and (arith-type? t1) (arith-type? t2))
         #:do[(current-Cs (cons (add-orig #`(>= #,t1 #,t2) #`(>= #,(get-orig t1) #,(get-orig t2)))
                                (current-Cs)))]
       #t]
      [_ #f]))))
  (current-typecheck-relation new-type-rel)
  
  ;; new type eval
  (define (lit-stx? x) (define y (stx-e x)) (or (string? y)))
  (define old-eval (current-type-eval))
  ;; TODO: need to assign outputs here with types?
  (define (new-eval t)
    (syntax-parse (old-eval t)
;      [t+ #:do [(printf "EVALing: ~a\n" (stx->datum #'t+))] #:when #f #'(void)]
      ;; check for singleton types (includes tyvars)
      ;; (singletons eliminates need to extra cases to handle specifics #%apps)
      ;; eg producer-length
      [t+ #:when (let ([k-as-ty (typeof #'t+)])
                   (and k-as-ty
                        (or (integer? (stx-e k-as-ty)) ; literal
                            (and (id? k-as-ty) (typecheck/Int? (typeof k-as-ty)))))); tyvar
          (mk-type/Int (typeof #'t+))]
      ;; number literals
      [((~literal quote) n:exact-nonnegative-integer) (assign-type #'n #'Nat)]
      [((~literal quote) s:str) #'s]
      [((~literal quote) b:boolean) #'b]
      [((~literal #%expression) e) ((current-type-eval) #'e)] ; and generates these #%exprs?
      ;; if
      [(~and orig ((~literal v:if) tst e1 e2))
       #:do [(define res ((current-type-eval) #'tst))]
       (if (boolean? (stx-e res))
           (if (stx-e res) ((current-type-eval) #'e1)  ((current-type-eval) #'e2))
           #'orig)]
      ;; #%app producer-length
      #;[((~literal #%plain-app) _ p)
       #:with (~literal v:producer-length) (syntax-property this-syntax 'orig-app)
       #:with (~Producer n) (typeof #'p)
       #'n]
      ;; #%app get-property
      [(~and orig ((~literal #%plain-app) _ p k))
       #:with (~literal v:get-property) (syntax-property this-syntax 'orig-app)
       #:do [(define k* (stx-e ((current-type-eval) #'k)))]
       #:when (string? k*)
       #:do [(define v (syntax-property #'p (string->symbol k*)))]
       (or (and v #`#,v) #'orig)]
      ;; #%app equal?
      [(~and orig ((~literal #%plain-app) (~literal v:equal?) e1 e2))
       #:with e1+ ((current-type-eval) #'e1)
       #:with e2+ ((current-type-eval) #'e2)
       (if (and (lit-stx? #'e1+) (lit-stx? #'e2+))
           #`#,(equal? (stx-e #'e1+) (stx-e #'e2+))
           #'orig)]
      ;; #%app >=
      [((~literal #%plain-app) (~literal v:>=) . args)
       #:with (~and ns
                   ((~or _:integer
                         ((~literal quote) _:integer))...))
              (stx-map (current-type-eval) #'args)
       #`#,(stx>= #'ns)]
      [((~literal #%plain-app) (~literal v:<=) . args)
       #:with (~and ns
                   ((~or _:integer
                         ((~literal quote) _:integer))...))
              (stx-map (current-type-eval) #'args)
       #`#,(stx<= #'ns)]
      ;; #%app +
      [((~literal #%plain-app) (~literal v:+) . args)
       #:with ((~or n:integer
                    ((~literal quote) m:integer)
                    other) ...) ; collect unsolved terms
              (stx-map (current-type-eval) #'args)
       (mk-type/Int
        (if (stx-null? (attribute other))
            #`#,(+ (stx+ #'(n ...)) (stx+ #'(m ...)))
            #`(#%plain-app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...)))]
      ;; #%app -
      [((~literal #%plain-app) (~literal v:-) a0 . args)
       #:with ((~or n:integer
                    ((~literal quote) m:integer)
                    other) ...) ; collect unsolved terms
                    (stx-map (current-type-eval) #'args)
       (mk-type/Int
        (syntax-parse ((current-type-eval) #'a0)
          [n0:integer
           #:with tmp #`#,(- (stx-e #'n0) (stx+ #'(n ...)) (stx+ #'(m ...)))
           (if (stx-null? (attribute other))
               #'tmp
               #`(#%plain-app v:- tmp other ...))]
          [((~literal quote) n0:integer)
           #:with tmp #`#,(- (stx-e #'n0) (stx+ #'(n ...)) (stx+ #'(m ...)))
           (if (stx-null? (attribute other))
               #'tmp
               #`(#%plain-app v:- tmp other ...))]
          [o0
           #:with tmp #`#,(+ (stx+ #'(n ...)) (stx+ #'(m ...)))
           #`(#%plain-app v:- o0 tmp other ...)]))]
      #;[((~literal #%plain-app) (~literal v:-) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       #`#,(stx- #'ns)]
      ;; #%app /
      [((~literal #%plain-app) (~literal v:quotient) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (mk-type/Int #`#,(stx/ #'ns))]
      ;; #%app min
      [((~literal #%plain-app) (~literal v:min) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (mk-type/Int #`#,(stx-min #'ns))]
      [(~Producer n)
       ;; TODO: just return inf if cant eval complicated arith expr
       ;; #:do [(printf "Producer with: ~a\n" (stx->datum #'n))
       ;;       (displayln (get-orig this-syntax))]
       #:with n- ((current-type-eval) #'n)
       ;       #:with out-n (if (number? (stx-e #'n-)) #'(#%datum . n-) #'n-)
       #:with n-/orig (syntax-parse #'n-
                        [_:exact-nonnegative-integer #'n-]
                        [_ (pass-orig #'n- #'n)])
       ;; #:with new-orig #`(Producer
       ;;                    #,(syntax-parse #'n-
       ;;                        [x:exact-nonnegative-integer (add-orig #'x #'x)]
       ;;                        [any (get-orig #'n-)]))
       (add-orig
        (mk-type (expand/df #'(Producer- n-/orig)))
        #`(Producer #,(get-orig #'n-/orig)))]
      [t+ #'t+]))
  (current-type-eval new-eval)

  (define (lookup Xs X+tys)
    (stx-map (λ (X) (lookup1 X X+tys)) Xs))
  (define (lookup1 Y X+tys)
    (and (not (stx-null? X+tys))
         (syntax-parse (stx-car X+tys)
           [(X:id ty) #:when (free-id=? Y #'X) #'ty]
           [_ (lookup1 Y (stx-cdr X+tys))])))

  ;; TODO: do something less naive
  (define (unify tysX tys)
    (stx-appendmap unify1 tysX tys))
  (define (unify1 tyX ty)
    (syntax-parse (list tyX ty)
      [((~Producer (_ (~literal v:-) n:id x)) (~Producer m))
       #'((n (+ m x)))]
      [((~Producer n:id) (~Producer m))
       #'((n m))]
      [_ '()]))

  (define current-Cs (make-parameter '()))
  ;; extract precise failing condition from many; for better err msg
  ;; check C, print CX when fail
  (define (Cs->str CX C)
    ;; (displayln (stx->datum CX))
    ;; (displayln (stx->datum C))
    (syntax-parse (list CX C)
      [(((~literal if-) e1 e2 _)
        ((~literal if-) e3 e4 _))
       (if (stx-e ((current-type-eval) #'e3))
           (Cs->str #'e2 #'e4)
           (Cs->str #'e1 #'e3))]
      [(((~literal #%expression) e1)
        ((~literal #%expression) e2))
       (Cs->str #'e1 #'e2)]
      ;; type->str doesnt work for some reason
      ;; It digs down too far, and replaces a var I want with another orig
      ;; and I cant figure out where it comes from
      ;; (see failing make-conf-talk example in paper-tests.rkt)
      [_ (format "~a" (stx->datum (get-orig CX)))]))
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
  #;[(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Nat] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ Nat]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ #,(assign-type #'(v:#%app v:+ e- ...) #'Int)]]) ; lift

(define-typed-syntax -
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:- ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:- e- ...) ⇒ #,(assign-type #'(v:#%app v:- e- ...) #'Int)]]) ; lift

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
   [⊢ e1 ≫ e1- ⇒ _] [⊢ e2 ≫ e2- ⇒ _]
   ----------
   [⊢ (v:#%app v:equal? e1- e2-) ⇒ Bool]])

(define-typed-syntax and
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ _] ...
   ----------
   [⊢ (v:and e- ...) ⇒ Bool]])

;; TODO: use singleton types?
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
(define-typed-syntax #%datum
  [(_ . n:exact-nonnegative-integer) ≫ ; use singleton types
   --------
   [⊢ (v:#%datum . n) ⇒ #,(add-orig (assign-type #'(v:#%datum . n) #'Nat) #'n)]]
  [(_ . n:integer) ≫ ; use singleton types
   --------
   [⊢ (v:#%datum . n) ⇒ #,(add-orig (assign-type #'(v:#%datum . n) #'Int) #'n)]]
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
   [([X ≫ X- : Int] ...) ([x ≫ x- : τ_in] ...) ⊢ [e ≫ e- ⇐ τ_out] [τ_in ≫ τ_in- ⇒ _] ... [τ_out ≫ τ_out- ⇒ _] [C0 ≫ C0- ⇒ _]]
   #:with new-orig
          (if (equal? #t (stx-e (stx-cadr #'C0-)))
              (cond [(null? (current-Cs)) #'()]
                    [(= 1 (length (current-Cs)))
                     (get-orig (car (current-Cs)))]
                    [else #`(and #,@(map get-orig (current-Cs)))])
              (if (null? (current-Cs))
                  (get-orig #'C0)
                  #`(and #,(get-orig #'C0) #,@(map get-orig (current-Cs)))))
   #:with C (add-orig
             #`(and C0- #,@(map syntax-local-introduce (current-Cs)))
             #'new-orig)
               #;(if (null? (current-Cs)) #'C0-
                ;; TODO: update orig: replace with X ...
                (car (map (λ (C) (syntax-local-introduce C) #;(substs #'(X ... x ...) #'(X- ... x- ...) (syntax-local-introduce C))) (current-Cs))))
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ #:bind (X- ...) τ_in- ... τ_out- #:when C)]] ; TODO: should be (and C0 C)?
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
;   #:do[(printf "applying ~a\n" (stx->datum (get-orig #'e_fn)))]
   [⊢ e_fn ≫ e_fn- ⇒ (~and ty-fn (~∀ (X ...+) ~! (~→ τ_inX ... τ_outX CX)))]
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ _ ⇒ τ_arg] ...
   ;; TODO: use return type (if known) to help unify
   #:with (X+ty ...) (unify #'(τ_inX ...) #'(τ_arg ...))
   #:with solved-tys (lookup #'(X ...) #'(X+ty ...))
   #:with (τ_in ... τ_out C)
          (substs #'solved-tys
                  #'(X ...)
                  #'(τ_inX ... τ_outX CX))
   #:with C- ((current-type-eval) #'C)
   ;; #:do[(printf "constraint POLY: ~a\n" (stx->datum #'CX))
   ;;      (printf "constraint POLY (orig): ~a\n" (type->str #'CX))
   ;;      (printf "constraint BEFORE: ~a\n" (stx->datum #'C))
   ;;      (printf "constraint AFTER: ~a\n" (stx->datum #'C-))]
   ;; TODO: improve this constraint check/propagate code
   #:fail-unless (stx-e #'C-) (format (string-join
                                       (list "while applying fn ~a"
                                             "failed condition: ~a"
                                             "inferred: ~a"
                                             "for function type: ~a")
                                       ";\n")
                                      (type->str #'e_fn-) ; fn
                                      (Cs->str #'CX #'C)  ; condition
                                      (string-join        ; inferred
                                       (map (λ (X ty)
                                              (syntax-parse ty
                                                [(_ n)
                                                 (string-append (type->str X) " = "
                                                                (number->string (stx->datum #'n)))]))
                                           (stx->list #'(X ...))
                                           (stx->list #'solved-tys))
                                       ",")
                                      (type->str #'ty-fn)) ; fn type
   #:do [(unless (or (boolean? (stx-e #'C-)) (boolean? (stx-e (stx-cadr #'C-))))
           (define (inst-orig e)
             (syntax-property
              e
              'orig
              (list (substs #'solved-tys
                            #'(X ...)
                            (get-orig e)
                            stx-datum=?))))
           ;; update C's orig with instantiation
           (define C-with-new-orig
             (let L ([C #'C])
               (inst-orig
                (syntax-parse C ; must update orig of each C individually
                  [((~literal if-) e1 e2 e3)
                   #`(if- #,(L #'e1) #,(L #'e2) #,(L #'e3))]
                  [((~literal #%expression) e)
                   #`(#%expression #,(L #'e))]
                  [e #'e]))))
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
  [(_ e_tst e1 e2) ⇐ τ-expected ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇐ τ-expected]
   [⊢ e2 ≫ e2- ⇐ τ-expected]
   --------
   [⊢ (v:if e_tst- e1- e2-)]]
  [(_ e_tst e1 e2) ≫
   [⊢ e_tst ≫ e_tst- ⇒ _] ; Any non-false value is truthy.
   [⊢ e1 ≫ e1- ⇒ τ1]
   [⊢ e2 ≫ e2- ⇒ τ2]
   --------
   [⊢ (v:if e_tst- e1- e2-) ⇒ (⊔ τ1 τ2)]])

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
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:blank n-) ⇒ #,(syntax/loc this-syntax (Producer n))]])

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

(provide (typed-out [[v:producer-length : (→ #:bind {n} (Producer n) n)]
                     producer-length]))
#;(define-typed-syntax (producer-length p) ≫
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
   [⊢ n ≫ n- ⇐ Int]
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
   [⊢ n ≫ n- ⇐ Int]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:length n-) ⇒ #,(stx/loc this-syntax (Producer n))]]
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
   [⊢ (v:#%app v:playlist p- ...) ⇒ #,(stx/loc this-syntax (Producer (+ n ...)))]]
  [(_ p1 p/t ... pn) ≫ ; producers + transitions
   [⊢ p1 ≫ p1- ⇒ (~Producer n1)]
   [⊢ pn ≫ pn- ⇒ (~Producer nn)]
   ;[⊢ p/t ≫ p/t- ⇒ (~or (~Producer n) (~Transition m))] ... ; doesnt work
   [⊢ p/t ≫ p/t- ⇒ P-or-T] ...
   #:with ((~or (~Producer n) (~Transition m)) ...) #'(P-or-T ...)
   ------------
   [⊢ (v:#%app v:playlist p1- p/t- ... pn-)
      ⇒ (Producer (- (+ n1 n ... nn) (+ m ...)))]]
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
  [(_ p #:end n) ≫
   [⊢ n ≫ n- ⇐ Int]
   [⊢ p ≫ p- ⇐ (Producer (+ 1 n))]
   -----------
   [⊢ (v:#%app v:cut-producer p- #:end n-) ⇒ (Producer (+ 1 n))]]
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
   --------
   [⊢ #,(syntax-property
         #'(v:#%app v:get-property p- k-)
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
