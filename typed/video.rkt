#lang turnstile
(require (for-syntax "stx-utils.rkt"))
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in video
                   #%app / #;producer-length ; manually provided
                   . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types
 λ #%datum define begin if let let* displayln
 + - min max <= >= < >
 list car cdr null null? hash equal? and
 producer-length
 blank color clip multitrack playlist external-video
 composite-transition fade-transition image
 scale-filter attach-filter grayscale-filter cut-producer
 get-property set-property)
(provide top-level-playlist require-vid #%type
         (rename-out [typed-app #%app]) /
         Producer Transition Filter (for-syntax ~Producer)
         Int Num Bool String Listof Hash Void →
         ann)

;; TODO:
;; - 2017-02-26: λ/video still not working
;; - 2017-02-13: #%module-begin define lifting not working for typed define
;;               DONE 2017-02-24
;; - 2017-03-03: most Nats (eg, for #:length args) should be Ints
;;               DONE 2017-03-03: removed Nat
;; - 2017-03-03: change #:end's to be exclusive, ie, n - m, not (add1 n - m)
;;               DONE 2017-03-04
;; - 2017-03-03: use actual +inf.0 instead of 99999
;; - 2017-03-03: remove orig-app property?
;; - 2017-03-03: switch more prims to use typed-out
;;               - requires creating fn type with kws and variable-arity
;; - 2017-03-03: add =, >, and <
;; - 2017-03-03: in playlist, check lengths of interleaved P/T?
;; - 2017-03-03: fix dependent use of regular fn args
;;               DONE 2017-03-06
;; - 2017-03-06: filter out dup Cs
;;               DONE 2017-03-06
;; - 2017-03-06: clean up matching of literals
;;               DONE 2017-03-06
;; - 2017-03-06: stx-OP should return stx?
;;               - typecheck? needs bool
;;               - but type-eval should return stx
;; - 2017-03-07: abstract constraint propagation

;; debugging NOTES:
;; 1) err: "bad syntax" on ids: look for stx+, eg in playlist or multitrack
;; 2) err: "expected Int": check type-eval for that case calls mk-type/Int
;; 3) err: "expected stx": check type-eval returns stx or that case

;; helpful unicode chars
;; ≫ τ ⊢ ⇒ ⇐ ≻ ∀ → (fn) ↑ (lift)

;; kinds ----------------------------------------------------------------------
(define-syntax-category :: kind)
  
;; types ----------------------------------------------------------------------
(define-binding-type ∀)
(define-type-constructor Listof)
(define-base-types String Int Num Bool Hash Void Filter)

(begin-for-syntax
  ;; fns for marking a type with kind Int
  (define Int+ (expand/df #'Int))
  (define (typecheck/Int? t) (typecheck? t Int+))
  (define (mk-type/Int t) (assign-type t Int+ #:wrap? #f))

  ;; lift e to type (with kind Int) and assign as e's type
  (define (lift/Int e) (assign-type e (mk-type/Int e)))
  ;; lift e to type (with kind Int) and assign as e's type
  (define (lift/Int* e+ e) (assign-type e+ (mk-type/Int e)))
  
  ;; handle arith exprs used as types
  (define (arith-type? t)
    (define ty-as-k (typeof t))
    (and ty-as-k
         (or ;; this case handles when arith expr is lifted to type
             ;; - check that kind of type is Int
             (typecheck/Int? ty-as-k)
             ;; this case handles when arith expr is written directly as type
             ;; - need to check the "type" of the kind
             (let ([ty-as-kk (typeof ty-as-k)])
               (and ty-as-kk (typecheck/Int? ty-as-kk))))))

  (current-type? (λ (t) (or (#%type? (kindof t)) (arith-type? t)))))

;; macro version of lift/Int
(define-syntax ↑/Int
  (syntax-parser [(_ e) (lift/Int #'e)]))
(define-syntax ↑/Int*
  (syntax-parser [(_ e+ e) (lift/Int* #'e+ #'e)]))

;; TODO: support kws in function type
(define-internal-type-constructor →)
;; full → stx: (→ #:bind (X:id ...) (x:id (~datum :) ty) ... ty-out #:when C)
;; - X: "type" vars with "kind" Int
;; - x: (possibly dependent) plain vars with type ty
;; - ty-out: output type
;; - C: constraint of type Bool
(define-kinded-syntax →
;  [a ≫ #:do[(displayln (stx->datum #'a))] #:when #f --- [≻ (void)]]
  ;; can't use :type stx class on input bc it needs X and x in context
  [(_ #:bind (X:id ...) (x:id (~datum :) ty) ... ty-out #:when C ~!) ≫
   [([X ≫ X- : Int] ...) ([x ≫ x- : ty] ...)
    ⊢ [ty ≫ ty-:type ⇒ : _] ...
      [ty-out ≫ ty-out-:type ⇒ : _]
      [C ≫ C- ⇐ : Bool]]
   ----------
   [≻ #,(add-orig
         #`(∀ (X- ...) (∀ (x- ...) #,(mk-type #'(→- ty- ... ty-out- C-))))
         #'(→ ty ... ty-out))]]
  [(_ #:bind (X:id ...) ty ... ty-out #:when C ~!) ≫
   #:with (x ...) (generate-temporaries #'(ty ...))
   ----------
   [≻ (→ #:bind (X ...) [x : ty] ... ty-out #:when C)]]
  [(_ #:bind (X:id ...) ty ...+) ≫
   ----------
   [≻ (→ #:bind (X ...) ty ... #:when #t)]]
  [(_ ty ...+) ≫
   ----------
   [≻ (→ #:bind () ty ...)]])

(define-for-syntax INF 999999)
(define-internal-type-constructor Producer)
(define-syntax (Producer stx)
  (define (set-orig-to-stx t) (add-orig t stx))
  (set-orig-to-stx
   (mk-type
    (syntax-parse stx
      ; TODO: this should use +inf.0 but using an int makes things easier for now
      [_:id #`(Producer- (v:#%datum . #,INF))] ; shorthand for inf length
      [(_ n:exact-nonnegative-integer) #'(Producer- n)]
      [(_ n) ; must accept Ints (as opposed to restricting to Nats), for -, etc
       #:with n- (ev #'n) ; let eval set orig
       ;; check type
       #:when (arith-type? #'n-) ; any Int arith expr arg is ok
       ;; commit to this clause, then check or propagate constraint
       #:with (~and ~! C-) ((current-type-eval) #'(v:#%app v:>= n- 0))
       #:fail-unless (stx-e #'C-)
                     (fmt "expression has type ~a, which fails side-condition: ~a"
                          (stx->datum this-syntax) (stx->datum #'(>= n 0)))
       ;; - Producer must propagate constraint bc instatiation wont expand surface-lvl
       ;; Producer, ie arg wont be re-checked to satisfy >= 0
       ;; - n- and C- must go through the same expansion, but type-eval also expands
       ;; so be careful here
       #:do [(unless (or (boolean? (stx-e #'C-)) (boolean? (stx-e (stx-cadr #'C-))))
               ;; (displayln (stx->datum #'n-))
               ;; (printf "or : ~a\n" (get-orig #'n-))
               ;; (printf "orn: ~a\n" (get-orig #'n))
               (add-C (add-orig #;(assign-type #'C- #'Bool #:wrap? #f) #'(>= n- 0)
                                #`(>= #,(get-orig #'n-) 0))))]
       #'(Producer- n-)]
      [(_ x) (type-error
              #:src stx
              #:msg
              "Producer: expected expression of type Int, given ~a with type ~a"
              #'x #`#,(typeof ((current-type-eval) #'x)))]))))

(define-internal-type-constructor Transition)
(define-syntax (Transition stx)
  (add-orig
   (mk-type
    (syntax-parse stx
      [_:id #'(Transition- 0)]
      [(_ n:exact-nonnegative-integer) #'(Transition- n)]))
   stx))

;; override typecheck-relation to consider numbers and other terms
(begin-for-syntax
  (define old-type? (current-type?))
  (current-type? (λ (t) (or (old-type? t) (Int-ty? (kindof t)))))

  ;; these preds assume expanded tys
  ;; - lowercase matches literals only, ie singletons
  ;; - uppercase includes general tys, eg Int
  (define int-ty? (syntax-parser [_:int #t][_ #f]))
  (define (Int-ty? t) (or (Int? t) (int-ty? t) (arith-type? t)))
  
  ;; new type relation: a subtyping relation
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    ;; (printf "t1 = ~a\n" (stx->datum t1))
    ;; (printf "t2 = ~a\n" (stx->datum t2))
    (and t1 t2 ; #f possible bc tys may have "type" (:) *or* kind #%type (::)
    (or
     (type=? t1 t2)
     (equal? (stx-e t1) (stx-e t2)) ; for singleton types
     (and (Int-ty? t1) (Num? t2))
     (and (Int-ty? t1) (Int? t2))
     (syntax-parse (list t1 t2)
      [(((~literal #%expression) e) _) (typecheck? #'e t2)] ; `and` generates these
      [(_ ((~literal #%expression) e)) (typecheck? t1 #'e)] ; `and` generates these
      [((~Listof x) (~Listof y))         (typecheck? #'x #'y)]
      [((~Producer m) (~Producer n))     (typecheck? #'m #'n)]
      [((~Transition m) (~Transition n)) (typecheck? #'m #'n)]
      [((~∀ Xs t1) (~∀ Ys t2))
        (and (stx-length=? #'Xs #'Ys)
             (typecheck? (substs #'Ys #'Xs #'t1) #'t2))]
      ;; TODO: enable checking of constraints in fns?
      [((~→ i ... o c) (~→ j ... p d)) (typechecks? #'(j ... o) #'(i ... p))]
      [(m:int n:int) (stx>= #'(m n))]
      [(b1:bool b2:bool) (stx-equal? #'(b1 b2))]
      ;; arith expr: sort + terms
      [(((~literal #%plain-app) (~literal v:+) . xs)
        ((~literal #%plain-app) (~literal v:+) . ys))
       (and (stx-length=? #'xs #'ys)
            (typechecks? (stx-sort #'xs) (stx-sort #'ys)))]
      ;; 2 Int exprs, not stx=?, so generate constraint
      [_ #:when (and (arith-type? t1) (arith-type? t2))
         #:do[(add-C (add-orig #`(>= #,t1 #,t2)
                               #`(>= #,(get-orig t1) #,(get-orig t2))))]
       #t]
      [_ #f]))))
  (current-typecheck-relation new-type-rel)
  
  ;; new type eval
  (define (lit-stx? x) (define y (stx-e x)) (or (string? y)))

  (define typechecking? (make-parameter #f))
  ;; TODO: need to assign outputs here with types?
  (define old-eval (current-type-eval))
  (define (new-eval t)
    (syntax-parse (old-eval t)
    ;(define-type-eval t
;      [t+ #:do [(printf "EVALing: ~a\n" (stx->datum #'t+))] #:when #f #'(void)]
      ;; check for singleton types (includes tyvars)
      ;; - singletons eliminates some cases to handle specific #%apps
      ;; eg producer-length
      ;; TODO: remove this case?
      ;; - shouldnt have terms like x : x :: Int lifted to the type level?
      ;; - should only lift x :: Int part instead?
      [t+
       #:do[(define k-as-ty (typeof #'t+))]
       #:when
       (let (#;[k-as-ty (typeof #'t+)])
         (and
          k-as-ty
          (or (integer? (stx-e k-as-ty)) ; literal
              (and (id? k-as-ty) (typecheck/Int? (typeof k-as-ty)))))); tyvar
       (mk-type/Int (typeof #'t+))]
      ;; number literals
      [n:int (mk-type/Int #'n.val)]
      [x:lit #'x.val] ; TODO: add type?
      [((~literal #%expression) e) ((current-type-eval) #'e)] ; `and` generates these #%exprs?
      ;; if
      [(~and orig ((~literal v:if) tst e1 e2))
       #:do [(define res (ev #'tst))]
       (if (boolean? (stx-e res))
           (if (stx-e res) (ev #'e1)  (ev #'e2))
           #'orig)]
      ;; #%app get-property
      [(~and orig ((~literal #%plain-app) _ p k))
       #:with (~literal v:get-property) (syntax-property this-syntax 'orig-app)
       #:with k*:string (ev #'k)
       #:do [(define v (syntax-property #'p (string->symbol (stx-e #'k*.val))))]
       (or (and v #`#,v) #'orig)]
      ;; #%app equal?
      [(~and orig ((~literal #%plain-app) (~literal v:equal?) e1 e2))
       #:with (x:lit y:lit) (type-evals #'(e1 e2))
       (stxx-equal? #'(x.val y.val))]
      ;; #%app >= and <=
      [((~literal #%plain-app) (~literal v:>=) . args)
       #:with ns:ints (type-evals #'args)
       (stxx>= #'ns.vals)]
      [((~literal #%plain-app) (~literal v:<=) . args)
       #:with ns:ints (type-evals #'args)
       (stxx<= #'ns.vals)]
      ;; #%app +
      [((~literal #%plain-app) (~literal v:+) . args)
       #:with ns:int+others (type-evals #'args)
       (mk-type/Int
        (if (stx-null? #'ns.rest)
            #'ns.sum
            (if (zero? (stx-e #'ns.sum))
                (add-orig #'(#%plain-app v:+ . ns.rest)
                          #'(+ . ns.rest))
                #'(#%plain-app v:+ ns.sum . ns.rest))))]
      ;; #%app -
      [((~literal #%plain-app) (~literal v:-) a0 . args)
       #:with ns:int+others (type-evals #'args)
       (mk-type/Int
        (syntax-parse (ev #'a0)
          [n0:int
           #:with tmp #`#,(- (stx-e #'n0.val) (stx-e #'ns.sum))
           (if (stx-null? #'ns.rest)
               #'tmp
               #`(#%plain-app v:- tmp . ns.rest))]
          [o0 (if (and (stx-null? #'ns.rest)
                       (zero? (stx-e #'ns.sum)))
                  #'o0
                  (add-orig #`(#%plain-app v:- o0 ns.sum . ns.rest)
                            #'(- o0 ns.sum . ns.rest)))]))]
      ;; #%app / (ie, quotient)
      [((~literal #%plain-app) (~literal v:quotient) . args)
       #:with ns:ints (type-evals #'args)
       (mk-type/Int (datum->stx t (stx/ #'ns.vals)))]
      ;; #%app min
      [((~literal #%plain-app) (~literal v:min) . args)
       #:with ns:ints (type-evals #'args)
       (mk-type/Int (datum->stx t (stx-min #'ns.vals)))]
      [(~Producer n)
       ;; TODO: return inf in some cases?
       #:with n- (syntax-parse (ev #'n)
                   [x:exact-nonnegative-integer (syntax-property #'x 'orig (list #'x))]
                   [x (pass-orig #'x #'n)])
       (add-orig
        (mk-type (expand/df #'(Producer- n-)))
        #`(Producer #,(get-orig #'n-)))]
      [t+ #'t+]))
  (current-type-eval
   (lambda (t)
     (parameterize ([typechecking? #t])
       (new-eval t))))
  (define (ev t) ((current-type-eval) t))

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
       #'((n (v:#%app v:+ m x)))]
      [((~Producer n:id) (~Producer m))
       #'((n m))]
      [_ '()]))


  ;; fns for manipulating constraints ---------------------
  (define current-Cs (make-parameter '()))

  (define (add-C C*)
    (define C (syntax-local-introduce C*))
    (unless (C-exists? C)
      (current-Cs (cons C (current-Cs)))))
  (define (C-exists? C)
    ;; dont use typecheck? will add unwanted constraints
    (ormap (λ (C0) (type=? C C0)) (current-Cs)))
  
  ;; extract precise failing condition from (and C ...), for better err msg
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
      ;; It digs down too far, and replaces var I want with another orig
      ;; and I cant figure out where it comes from
      ;; (see failing make-conf-talk example in paper-tests.rkt)
      [_ #;(type->str CX) (format "~a" (stx->datum (get-orig CX)))]))

  (define (Cs-map f Cs)
    (let L ([C Cs])
      (f
       (syntax-parse C
         [((~literal if-) e1 e2 e3)
          (assign-type #`(if- #,(L #'e1) #,(L #'e2) #,(L #'e3)) #'Bool)]
         [((~literal #%expression) e) #`(#%expression #,(L #'e))]
         [e #'e]))))

  ;; Adds given C- to (current-Cs)
  ;; Returns stx obj suitable for use in program,
  ;; ie, the Cs are combined with `and`, with a nice 'orig property
  (define (merge-Cs C- #:orig C)
    (define orig
      (if (equal? #t (stx-e C))
          ; drop #t in (and #t ...) for err msgs
          ; TODO: does this catch cases where C tyeval's to #t (?)
          (cond [(null? (current-Cs)) #'()]
                [(= 1 (length (current-Cs)))
                 (get-orig (car (current-Cs)))]
                [else #`(and #,@(map get-orig (current-Cs)))])
          (if (null? (current-Cs))
              (get-orig C)
              #`(and #,(get-orig C) #,@(map get-orig (current-Cs))))))
    (add-orig
     #`(and #,C- #,@(map syntax-local-introduce (current-Cs)))
     orig))

  (define (X+tys->str Xs tys) ; Xs are tyvars and tys are numbers
    (string-join
     (stx-map
      (λ (X ty) (++ (type->str X) " = " (num->str (stx->num ty))))
      Xs tys)
     ","))
  )

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
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:max e- ...) ⇒ Int]])

(define-typed-syntax +
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [≻ (↑/Int* (v:#%app v:+ e- ...) (v:#%app v:+ e ...))]])

(define-typed-syntax -
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [≻ (↑/Int* (v:#%app v:- e- ...) (v:#%app v:- e ...))]])

;; integer divide
(define-typed-syntax /
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
;; for now, only use these at the type level
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
;; copied from turnstile/examples/stlc+cons.rkt
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
  [(_ x ...) ⇐ (~Listof τ) ≫ ; has expected type
   [⊢ x ≫ x- ⇐ τ] ...
   --------
   [⊢ (v:#%app v:list x- ...) ⇒ (Listof τ)]]
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
  [(_ . n:integer) ≫ ; use singleton types
   --------
   [≻ (↑/Int (v:#%datum . n))]]
  [(_ . n:number) ≫ ; Num needed by composite-transition
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
  ;; define for values ------------------------------------
  [(_ x:id e) ≫
   [⊢ e ≫ e- ⇒ τ]
   #:with y+props (transfer-props #'e- (assign-type #'y #'τ #:wrap? #f))
   --------
   [≻ (begin- ; TODO: make typed-variable-rename also transfer props?
              (define-typed-variable-rename x ≫ y+props : τ)
              (define- y  e-))]]
  ;; define for functions ---------------------------------
  ;; polymorphic: explicit forall, TODO: infer tyvars
  [(_ (f Xs [x (~datum :) ty] ... (~optional (~seq #:when C) #:defaults ([C #'#t]))
            (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:when (brace? #'Xs)
   ;; expanding the λ here means mutual recursion wont work
   ;; but need to to get back τ_f, which may contain new constraints
   ;; (when compared to ty-expected)
   [⊢ (λ Xs ([x : ty] ... #:when C -> ty_out) (begin e ...)) ≫ lam- ⇒ τ_f]
   #:with f- (fresh #'f)
   --------
   [≻ (begin- (define-typed-variable-rename f ≫ f- : τ_f)
              (define- f- lam-))]]
  ;; monomorphic case
  [(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   --------
   [≻ (define (f {} [x : ty] ... -> ty_out) e ...)]])

(define-typed-syntax λ #:datum-literals (:)
  ;; TODO: remove dup clauses? (first one just has extra -> ty-out pat)
  [(_ (~and Xs (~fail #:unless (brace? #'Xs)) {X ...})
      ((~and ; 1st pat: all input types (for use in resulting fn type);
             ; need this case to preserve order of args
             ; (which gets mixed up by the next pattern)
             (~seq [_:id (~datum :) τ_in] ...)
             ; 2nd pat: separate Ints (use in ty env to lift int vars)
             ; TODO: better way to match Int types than with ~literal?
             (~seq (~or [i:id (~datum :) (~literal Int)]
                        [o:id (~datum :) tyo]) ...))
       #:when C0 (~datum ->) τ_out) e ~!) ≫
   #:do[(current-Cs '())] ; reset Cs; this is essentially parameterize
   #:with (i* ...) (stx-map fresh #'(i ...))
   #:with (i-as-ty ...) (stx-map mk-type/Int #'(i* ...))
   #:with ([x tyx] ...) #`([i i-as-ty] ... [o tyo] ...)
   ;; need to bind x ... (ie i ... o ...) for both term and type
   ;; PREVIOUSLY: added x : x :: Int to type env,
   ;;  where x the type was bound bc int-def-ctx binds recursively,
   ;;  but did not expand to x-, causing subst problems in typed-app
   ;; NOW: add indirection i* ..., and explicitly bind it in type env,
   ;;  and add x : i* :: Int to type env,
   ;;  then use x- to bind term and i*- to bind type
   [([X ≫ X- : Int] ...) ([i* ≫ i*- : Int] ...) ([x ≫ x- : tyx] ...)
    ⊢ [e ≫ e- ⇐ τ_out]
    ;; can't use :type stx class on input bc it needs X and x in context
    [τ_in ≫ τ_in-:type ⇒ :: _] ...
    [τ_out ≫ τ_out-:type ⇒ :: _]
    [C0 ≫ C0- ⇐ Bool]]
   #:with C (merge-Cs #'C0- #:orig #'C0)
   #:with (o- ...) (stx-drop #'(x- ...) (stx-length #'(i ...)))
   ;; NOTE: the xs are in different order than surface program
   ;; - but that is ok since they are only used for polymorphic inst in typed-app
   ;; - the τ_in- are still in order, which is what matters
   #:with (x+tin ...) (stx-map (λ (x t) #`[#,x : #,t]) #'(i*- ... o- ...) #'(τ_in- ...))
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ #:bind (X- ...) x+tin ... τ_out- #:when C)]]
  ;; similar to first case but no return type
  ;; TODO: separate Int args, like in first case
  [(_ (~and Xs (~fail #:unless (brace? #'Xs)) {X ...})
      ([x:id (~datum :) τ_in] ... #:when C0) e) ≫
   #:do[(current-Cs '())] ; reset Cs; this is essentially parameterize
   [([X ≫ X- : Int] ...) ([x ≫ x- : τ_in] ...)
    ⊢ [e ≫ e- ⇒ τ_out] [τ_in ≫ τ_in-:type ⇒ :: _] ... [C0 ≫ C0- ⇐ Bool]]
   #:with C (merge-Cs #'C0- #:orig #'C0)
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ #:bind (X- ...) [x- : τ_in-] ... τ_out #:when C)]]
  ;; no explicit tyvars
  [(_ ([x:id (~datum :) τ_in] ...) e) ≫
   -------
   [≻ (λ {} ([x : τ_in] ... #:when #t) e)]])

(define-typed-syntax typed-app
  [(_ e_fn e_arg ...) ≫ ; polym, must instantiate
   [⊢ e_fn ≫ e_fn- ⇒ (~and ty-fn (~∀ (X ...) ~! (~∀ (x ...) (~→ τ_inX ... τ_outX CX))))]
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                  (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ e_arg- ⇒ τ_arg] ...
   ;; TODO: use return type (if known) to help unify
   #:with (X+ty ...) (unify #'(τ_inX ...) #'(τ_arg ...))
   #:with solved-tys (lookup #'(X ...) #'(X+ty ...))
   #:do[(define (inst e [id=? bound-id=?])
          (substs (stx-append #'solved-tys #'(e_arg- ...))
                  ; TODO: filter non-Int xs?
                  ; actually, no filtering should be ok?
                  ; non-Ints would have erred already if used improperly
                  #'(X ... x ...)
                  e
                  id=?))
        (define (inst-orig e)
          (syntax-property e 'orig (list (inst (get-orig e) stx-datum=?))))
        (define (do-inst e)
          (inst-orig (inst e)))]
   #:with (τ_in ... τ_out C) (stx-map do-inst #'(τ_inX ... τ_outX CX))
   #:with C- ((current-type-eval) #'C)
   ;; if fail, search for precise C in (and C ...), to avoid a large err msg
   #:fail-unless (stx-e #'C-) (format (string-join
                                       (list "while applying fn ~a"
                                             "failed condition: ~a"
                                             "inferred: ~a"
                                             "for function type: ~a")
                                       ";\n")
                                      (type->str #'e_fn-) ; fn
                                      (Cs->str #'CX #'C)  ; condition
                                      ; TODO: also print e_arg?
                                      (X+tys->str #'(X ...) #'solved-tys) ; inferred
                                      (type->str #'ty-fn)) ; fn type
   ;; else propagate C
   #:do [(unless (or (boolean? (stx-e #'C-)) (boolean? (stx-e (stx-cadr #'C-))))
           ;; instantiate Cs orig before propagating
           (add-C (Cs-map inst-orig #'C)))]
   ;; #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
   ;;               (format "app failed ~a" (stx->datum this-syntax))
   [⊢ e_arg ≫ _ ⇐ τ_in] ... ; double expand?
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
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:color c- #:length n-) ⇒ (Producer n)]])

(define-typed-syntax image
  [(_ f) ≫
   [⊢ f ≫ f- ⇐ String]
   --------
   [⊢ (v:#%app v:clip f-) ⇒ Producer]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:length n-) ⇒ (Producer n)]])

;; returns length or false
(define-for-syntax (get-clip-len f)
  (with-handlers ([exn? (λ _ #f)])
    (parameterize ([current-namespace (make-base-namespace)])
      (namespace-require 'video)
      (eval `(get-property
              (clip ,(syntax->datum f))
              "length" 'int)))))
(define-typed-syntax clip
  [(_ f) ≫ ; literal arg
   [⊢ f ≫ f- ⇐ String]
   #:do [(define len (get-clip-len #'f))]
   --------
   [⊢ (v:#%app v:clip f-) ⇒ #,(or (and len #`(Producer #,len))
                                  #'Producer)]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
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
   #:do [(define len (get-clip-len #'f))]
   [⊢ n ≫ n- ⇐ 0]
   [⊢ m ≫ m- ⇐ 0]
   [⊢ #,(or len INF) ≫ _ ⇐ (- m n)]
   --------
   [⊢ (v:#%app v:clip f- #:start n- #:end m-) ⇒ (Producer (- m n))]])

(define-typed-syntax producer-length
  [(_ p) ≫
   [⊢ p ≫ p- ⇒ (~Producer n)]
   -------
   [⊢ #,(if (typechecking?) #'n #'(v:#%app v:producer-length p-)) ⇒ n]])
      
#;(define-syntax producer-length
  (make-variable-like-transformer
   (assign-type #'v:producer-length #'(→ #:bind {n} [x : (Producer n)] n #:when #t) #:wrap? #f)))
;(provide producer-length)
#;(provide (typed-out [[v:producer-length : (→ #:bind {n} [x : (Producer n)] n #:when #t)]
                     producer-length]))

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

(define-typed-syntax playlist
  [(_ p ... #:transitions ~! t ...) ≫ ; producers + transitions, kw
   ; t's must interleave p's
   #:fail-unless (and (= (stx-length #'(p ...)) (add1 (stx-length #'(t ...)))))
                 "insufficient number of transitions"
   [⊢ t ≫ t- ⇒ (~Transition m)] ...
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   #:with (p0 p1 ...) #'(p ...)
   #:with (pa ... pb) #'(p ...)
   ;; TODO: eliminate double-expansions?
   [⊢ p1 ≫ _ ⇐ (Producer m)] ...
   [⊢ pa ≫ _ ⇐ (Producer m)] ...
   ------------
   [⊢ (v:#%app v:playlist p- ... #:transitions (v:list t- ...))
      ⇒ (Producer (- (+ n ...) (+ m ...)))]]
  [(_ p ...) ≫ ; producers only
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ------------
   [⊢ (v:#%app v:playlist p- ...) ⇒ #,(stx/loc this-syntax (Producer (+ n ...)))]]
  [(~and pl (_ p/t ...)) ≫ ; producers + transitions, inline
   [⊢ p/t ≫ p/t- ⇒ P-or-T] ...
   ; TODO: improve this manual validation
   #:when (let L ([p/ts #'(p/t ...)] [tys #'(P-or-T ...)] [origs #'(p/t ...)])
            (syntax-parse (list p/ts tys origs)
              [(() _ _) #t]
              [((p1 t p2 . rst)
                ((~Producer n1)
                 (~Transition m)
                 (~and ty2 (~Producer n2)) . tyrst)
                (op1 ot op2 . orst))
               (and
                (or (typecheck? #'n1 #'m)
                    (type-error #:src #'pl
                     #:msg
                     (fmt
                      "playlist: transition ~a (~a:~a) too long for adjacent producer ~a (~a:~a)"
                      (type->str #'ot)
                      (syntax-line #'ot) (syntax-column #'ot)
                      (type->str #'op1)
                      (syntax-line #'op1) (syntax-column #'op1))))
                (or (typecheck? #'n2 #'m)
                    (type-error #:src #'pl
                     #:msg
                     (fmt
                      "playlist: transition ~a (~a:~a) too long for adjacent producer ~a (~a:~a)"
                      (type->str #'ot)
                      (syntax-line #'ot) (syntax-column #'ot)
                      (type->str #'op2)
                      (syntax-line #'op2) (syntax-column #'op2))))
                    (L #'(p2 . rst) #'(ty2 . tyrst) #'(op2 . orst)))]
              [((_ . rst) ((~Producer _) . tyrst) (_ . orst))
               (L #'rst #'tyrst #'orst)]
              [_ #f]))
   #:with ((~or (~Producer n) (~Transition m)) ...) #'(P-or-T ...)
   ------------
   [⊢ (v:#%app v:playlist p/t- ...)
      ⇒ (Producer (- (+ n ...) (+ m ...)))]]
  [xs ≫
   ------------
   [#:error
    (type-error
     #:src #'xs
     #:msg "playlist must interleave producers and transitions, given: ~v"
     #'xs)]])
(define-typed-syntax top-level-playlist
  [(_ p ...) ≫
   ;; "run" tests (via expansion)
   #:with ps- (expands/stop #'(p ...))
   ;; but dont include in runtime program
   #:with ((p* _) ...) (stx-filter-out-false #'ps- (stx-map typeof #'ps-))
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
   [⊢ t ≫ t- ⇒ (~Producer _)]
   [⊢ b ≫ b- ⇒ (~Producer _)]
   --------
   [⊢ (v:#%app v:composite-transition x- y- w- h- #:top t- #:bottom b-)
      ⇒ Transition]])

(define-typed-syntax fade-transition
  [(_ #:length n:exact-nonnegative-integer) ≫
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:fade-transition #:length n-) ⇒ (Transition n)]]
  [(_ #:length n) ≫
   [⊢ n ≫ n- ⇐ Int]
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
  [(_) ≫
;   [⊢ p ≫ p- ⇒ (~and ty_out (~Producer _))]
   -----------
   [⊢ (v:#%app v:grayscale-filter) ⇒ Filter]])

(define-typed-syntax attach-filter
  [(_ p f ...) ≫
   [⊢ p ≫ p- ⇒ (~and ty_out (~Producer _))]
   [⊢ f ≫ f- ⇐ Filter] ...
   -----------
   [⊢ (v:#%app v:attach-filter p- f- ...) ⇒ ty_out]])

(define-typed-syntax cut-producer
  [(_ p (~optional (~seq #:start m) #:defaults ([m #'0]))
        (~optional (~seq #:end n/#f))) ≫
   [⊢ m ≫ m- ⇐ 0]
   [⊢ p ≫ p- ⇒ (~Producer len)]
   #:with n (if (attribute n/#f) #'n/#f #'len)
   [⊢ n ≫ n- ⇐ m] ; end (or len) >= start
   [⊢ p ≫ _ ⇐ (Producer n)]
   -----------
   [⊢ (v:#%app v:cut-producer p- #:start m- #:end n-) ⇒ (Producer (- n m))]])
   

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

(define-typed-syntax external-video
 [(_ v (~optional (~seq #:start m #:end n/#f) #:defaults ([m #'0]))) ≫
  [⊢ v ≫ _ ⇐ String]
  #:with tmp (generate-temporary)
  #:with vid (datum->syntax #'v 'vid)
  #:with vid-ty2 (datum->syntax #'v 'vid-ty2)
  #:with (_ () (_ () e-))
         (expand/df
          #'(let-syntax-
             ([tmp (make-variable-like-transformer
                    (let ([len (dynamic-require 'v 'vid-ty2)])
                      (syntax-property
                       #'(dynamic-require 'v 'vid)
                       ':
                       (add-orig
                        ((current-type-eval) #`(Producer #,len))
                        #`(Producer #,len)))))])
             tmp))
   #:with n (if (attribute n/#f) #'n/#f #`#,(dynamic-require (stx->datum #'v) 'vid-ty2))
   [⊢ m ≫ m- ⇐ 0]
   [⊢ n ≫ n- ⇐ m] ; end >= start
   [⊢ e- ≫ _ ⇐ (Producer n)] ; len >= end (and start)
   --------
   [⊢ e- ⇒ (Producer (- n m))]])

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
           (assign-type #'v-vid #'v-vid-ty #:wrap? #f))))]])
