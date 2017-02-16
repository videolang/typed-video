#lang turnstile
(require (for-syntax "stx-utils.rkt"))
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in video . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types
 λ #%app + - / min max #%datum define begin if let let* displayln
 list car cdr null null?
 blank color image clip multitrack playlist
 composite-transition fade-transition scale-filter attach-filter cut-producer
 get-property set-property producer-length)
(provide AnyProducer Producer Transition Filter
         Int Num Bool String Listof →
         ann)

;; TODO:
;; - 2017-02-13: #%module-begin define lifting not working for typed define

;; NOTES:
;; if getting "bad syntax" on ids, look for stx+, eg in playlist or multitrack

; ≫ τ ⊢ ⇒ ⇐ ≻ ∀

;; types ----------------------------------------------------------------------
(define-syntax-category :: kind)
(define-base-types String Int Num Bool Void Filter)
(define-type-constructor Listof)
(define-binding-type ∀)
;; TODO: support kws in function type
(define-internal-type-constructor →)
(define-kinded-syntax →
  [(_ #:bind (X ...) ty ...+) ≫
   [[X ≫ X- : Int] ... ⊢ [ty ≫ ty- ⇐ #%type] ...]
   ----------
   [≻ #,(add-orig #`(∀ (X- ...) #,(mk-type #'(→- ty- ...))) #'(→ ty ...))]]
  [(_ ty ...+) ≫
   [⊢ ty ≫ ty- ⇐ #%type] ...
   -----------
   [≻ #,(add-orig #`(∀ () #,(mk-type #'(→- ty- ...))) #'(→ ty ...))]])
(define-internal-type-constructor Producer)
(define-syntax (Producer stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Producer- 99999)) stx)] ; TODO: make this inf?
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Producer- n)) stx)]
    [(_ n)
     #:with n- (expand/df #'n)
     #:when (Int? (typeof #'n-)) ; any Int *expression* is ok as the type
     (mk-type #'(Producer- n-))]
    [(_ x) (type-error
            #:src stx
            #:msg "Producer: expected expression of type Int, given ~a" #'x)]))
(define-internal-type-constructor Transition)
(define-syntax (Transition stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Transition- (v:#%datum . 0))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Transition- n)) stx)]))

;; override typecheck-relation to consider numbers
(begin-for-syntax
  ;; new type relation: a subtyping relation
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    ;; (printf "t1 = ~a\n" (stx->datum t1))
    ;; (printf "t2 = ~a\n" (stx->datum t2))
    (or
     ((current-type=?) t1 t2)
     (and (Int? t1) (Num? t2))
     (syntax-parse (list t1 t2)
      [((~Listof x) (~Listof y))         (typecheck? #'x #'y)]
      [((~Producer m) (~Producer n))     (typecheck? #'m #'n)]
      [((~Transition m) (~Transition n)) (typecheck? #'m #'n)]
      [((~∀ Xs t1) (~∀ Ys t2))
        (and (stx-length=? #'Xs #'Ys)
             (typecheck? (substs #'Ys #'Xs #'t1) #'t2))]
      [((~→ i ... o) (~→ j ... p)) (typechecks? #'(j ... o) #'(i ... p))]
      [(((~literal quote) m:number) ((~literal quote) n:number))
       (>= (stx-e #'m) (stx-e #'n))]   ; longer vid is "more precise"
      [(_ ((~literal quote) n:number)) ; AnyProducer needs this
       #:when (zero? (stx-e #'n))
       #t]
      ;; arith expr: sort
      [(((~literal #%plain-app)
         (~and op1 (~or (~literal v:+) (~literal v:/) (~literal v:-))) . xs)
        ((~literal #%plain-app)
         (~and op2 (~or (~literal v:+) (~literal v:/) (~literal v:-))) . ys))
       (and (free-id=? #'op1 #'op2)
            (stx-length=? #'xs #'ys)
            (typechecks? (stx-sort #'xs) (stx-sort #'ys)))]
      [_ #f])))
  (current-typecheck-relation new-type-rel)
  
  ;; new type eval
  (define old-eval (current-type-eval))
  (define (new-eval t)
    (syntax-parse (old-eval t)
;      [t+ #:do [(printf "EVALing: ~a\n" (stx->datum #'t+))] #:when #f #'(void)]
      ;; number literals
      [((~literal quote) n:exact-nonnegative-integer) #'n]
      ;; #%app producer-length
      [((~literal #%plain-app) p-len p)
       #:with (~literal v:producer-length) (syntax-property this-syntax 'orig-app)
       #:with (~Producer n) (typeof #'p)
       #'n]
      ;; #%app +
      [((~literal #%plain-app) (~literal v:+) . args)
       #:with ((~or n:integer
                    ((~literal quote) m:integer)
                    other) ...) ; collect unsolved terms
              (stx-map (current-type-eval) #'args)
       (if (stx-null? (attribute other))
           (+ (stx+ #'(n ...)) (stx+ #'(m ...)))
           #`(#%plain-app v:+ #,(+ (stx+ #'(n ...)) (stx+ #'(m ...))) other ...))]
      ;; #%app -
      [((~literal #%plain-app) (~literal v:-) . args)
       #:with (~and ns
                   ((~or _:exact-nonnegative-integer
                    ((~literal quote) _:exact-nonnegative-integer))...))
              (stx-map (current-type-eval) #'args)
       (stx- #'ns)]
      ;; #%app /
      [((~literal #%plain-app) (~literal v:/) . args)
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
   #:with (e* ...) (remove-duplicates (attribute e) free-id=?)
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
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ Int]])

(define-typed-syntax -
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:- ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:- e- ...) ⇒ Int]])

(define-typed-syntax /
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:/ e- ...) ⇒ Int]])

;; lists ----------------------------------------------------------------------
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

;; Racket core forms ----------------------------------------------------------
(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (v:#%datum . n) ⇒ Int]]
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
  ;; explicit forall, TODO: infer tyvars
  [(_ (f Xs [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:when (brace? #'Xs)
   #:with f- (add-orig (generate-temporary #'f) #'f)
   #:with ty-expected #'(→ #:bind Xs ty ... ty_out)
   --------
   [≻ (begin-
        (define-syntax- f (make-rename-transformer (⊢ f- : ty-expected)))
        (define- f-
          (ann (λ (x ...) (begin e ...)) : ty-expected)))]]
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
  [(_ (x ...) e) ⇐ (~∀ (X ...) (~→ τ_in ... τ_out)) ≫
   [(X ...) ([x ≫ x- : τ_in] ...) ⊢ e ≫ e- ⇐ τ_out]
   -------
   [⊢ (v:λ (x- ...) e-)]]
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫ ; TODO: add forall?
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (v:λ (x- ...) e-)]])

(define-typed-syntax #%app
  [(_ e_fn e_arg ...) ≫ ;; must instantiate
   [⊢ e_fn ≫ e_fn- ⇒ (~∀ (X ...+) ~! (~→ τ_inX ... τ_outX))]
   #:fail-unless (stx-length=? #'[τ_inX ...] #'[e_arg ...])
                 (num-args-fail-msg #'e_fn #'[τ_inX ...] #'[e_arg ...])
   [⊢ e_arg ≫ _ ⇒ τ_arg] ...
   #:with (X+ty ...) (unify #'(τ_inX ...) #'(τ_arg ...))
   #:with (τ_in ... τ_out)
          (substs (lookup #'(X ...) #'(X+ty ...)) #'(X ...) #'(τ_inX ... τ_outX))
   ;; #:fail-unless (typechecks? #'(τ_arg ...) #'(τ_in ...))
   ;;               "TODO: change orig to inst"
   [⊢ e_arg ≫ e_arg- ⇐ τ_in] ... ; double expand?
   --------
   [⊢ (v:#%app e_fn- e_arg- ...) ⇒ τ_out]]
  [(_ e_fn e_arg ...) ≫ ;; non-polymorphic
   [⊢ e_fn ≫ e_fn- ⇒ (~∀ () ~! (~→ τ_in ... τ_out))]
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
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:color c- #:length n-) ⇒ (Producer n)]])

(define-typed-syntax image
  [(_ f) ≫
   [⊢ f ≫ f- ⇐ String]
   --------
   [⊢ (v:#%app v:image f-) ⇒ Producer]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:image f- #:length n-) ⇒ (Producer n)]])

;; TODO: read clip at compile time
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
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:length n-) ⇒ (Producer n)]]
  [(_ f #:start n #:end m) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   [⊢ m ≫ m- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:start n- #:end m-) ⇒ (Producer (+ (- m n) 1))]])

(define-typed-syntax (producer-length p) ≫
  [⊢ p ≫ p- ⇒ (~Producer _)]
  ---------
  [⊢ #,(syntax-property
        #'(v:#%app v:producer-length p-)
        'orig-app
        #'v:producer-length) ⇒ Int])

;; playlist combinators -------------------------------------------------------
;; TODO: should be interleaved Transition and Producer?
(define-typed-syntax multitrack
  [(_ (~and p (~not _:keyword)) ... #:transitions trans #:length n) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)] ...
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:transitions trans-) ⇒ (Producer n)]]
  [(_ (~and p (~not _:keyword)) ... #:transitions trans) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)] ...
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:transitions trans-) ⇒ Producer]]
  [(_ (~and p (~not _:keyword)) ... #:length n) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:when (stx-andmap (λ (t) (or (Transition? t) (Producer? t))) #'(ty ...))
   [⊢ n ≫ n- ⇐ Int]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:length n-) ⇒ (Producer n)]]
  [(_ p ...) ≫ ; producers only
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ------------
   [⊢ (v:#%app v:multitrack p- ...) ⇒ (Producer (min n ...))]]
  [(_ p ...) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:when (stx-andmap (λ (t) (or (Transition? t) (Producer? t))) #'(ty ...))
   ------------
   [⊢ (v:#%app v:multitrack p- ...) ⇒ Producer]])

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
   
(define-typed-syntax attach-filter
  [(_ p f ...) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)]
   [⊢ f ≫ f- ⇐ Filter] ...
   -----------
   [⊢ (v:#%app v:attach-filter p- f- ...) ⇒ Producer]])

(define-typed-syntax cut-producer
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
   [⊢ (v:#%app v:get-property p- k-) ⇒ String]]
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
