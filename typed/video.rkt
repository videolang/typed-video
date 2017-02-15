#lang turnstile
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in video . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types
 λ #%app + / #%datum define begin if let let*
 list car cdr null null?
 blank color image clip multitrack playlist
 composite-transition fade-transition scale-filter attach-filter
 get-property set-property producer-length)
(provide Producer Transition Filter
         Int Num Bool String Listof →
         ann)

;; TODO:
;; - 2017-02-13: #%module-begin define lifting not working for typed define

;; override typecheck-relation to consider numbers
(begin-for-syntax
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    (define t1* (stx->datum t1))
    (define t2* (stx->datum t2))
    (or (and (number? t1*) (number? t2*) (<= t1* t2*))
        (and (Int? t1) (Num? t2))
        (old-type-rel t1 t2)))
  (current-type=? new-type-rel)
  (current-typecheck-relation new-type-rel))

; ≫ τ ⊢ ⇒ ⇐

;; types ----------------------------------------------------------------------
(define-base-types String Int Num Bool Filter)
(define-type-constructor Listof)
;; TODO: support kws in function type
(define-type-constructor → #:arity > 0)
(define-internal-type-constructor Producer)
(define-syntax (Producer stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Producer- (v:#%datum . +inf.0))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Producer- n)) stx)]))
(define-internal-type-constructor Transition)
(define-syntax (Transition stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Transition- (v:#%datum . +inf.0))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Transition- n)) stx)]))

;; prims ----------------------------------------------------------------------
(define-typed-syntax +
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ Int]])

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

;; core forms -----------------------------------------------------------------
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

(define-typed-syntax λ #:datum-literals (:)
  [(_ ([x:id : τ_in:type] ...) e) ≫
   [[x ≫ x- : τ_in.norm] ... ⊢ e ≫ e- ⇒ τ_out]
   -------
   [⊢ (v:λ (x- ...) e-) ⇒ (→ τ_in.norm ... τ_out)]]
  [(_ (x:id ...) e) ⇐ (~→ τ_in ... τ_out) ≫
   [[x ≫ x- : τ_in] ... ⊢ e ≫ e- ⇐ τ_out]
   ---------
   [⊢ (v:λ (x- ...) e-)]])

(define-typed-syntax (#%app e_fn e_arg ...) ≫
  [⊢ e_fn ≫ e_fn- ⇒ (~→ τ_in ... τ_out)]
  #:fail-unless (stx-length=? #'[τ_in ...] #'[e_arg ...])
                (num-args-fail-msg #'e_fn #'[τ_in ...] #'[e_arg ...])
  [⊢ e_arg ≫ e_arg- ⇐ τ_in] ...
  --------
  [⊢ (v:#%app e_fn- e_arg- ...) ⇒ τ_out])

(define-typed-syntax (ann e (~datum :) τ:type) ≫
  [⊢ e ≫ e- ⇐ τ.norm]
  --------
  [⊢ e- ⇒ τ.norm])

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

;; TODO: add length polymorphism
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
  [(_ (f [x (~datum :) ty] ... (~or (~datum →) (~datum ->)) ty_out) e ...+) ≫
   #:with f- (add-orig (generate-temporary #'f) #'f)
   --------
   [≻ (begin-
        (define-syntax- f
          (make-rename-transformer (⊢ f- : (→ ty ... ty_out))))
        (define- f-
          (λ ([x : ty] ...)
            (ann (begin e ...) : ty_out))))]])

(define-typed-syntax begin
  [(_ e_unit ... e) ⇐ τ_expected ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇐ τ_expected]
   --------
   [⊢ (begin- e_unit- ... e-)]]
  [(_ e_unit ... e) ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇒ τ_e]
   --------
   [⊢ (begin- e_unit- ... e-) ⇒ τ_e]])

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

;; basic producers ------------------------------------------------------------
(define-typed-syntax blank
  [(_ n:exact-nonnegative-integer) ≫
   --------
   [⊢ (v:#%app v:blank n) ⇒ (Producer n)]]
  ;; TODO: use eval when not literal?
  [(_ n) ≫
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:blank n) ⇒ Producer]])

;; TODO: abstract definitions of these producers
;; TODO: add HO case
(define-typed-syntax color
  [(_ c) ≫
   [⊢ c ≫ c- ⇐ String]
   --------
   [⊢ (v:#%app v:color c-) ⇒ Producer]]
  [(_ c #:length n:exact-nonnegative-integer) ≫
   [⊢ c ≫ c- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:color c- #:length n-) ⇒ (Producer n)]]
  [(_ c #:length n) ≫
   [⊢ c ≫ c- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:color c- #:length n-) ⇒ Producer]])

(define-typed-syntax image
  [(_ f) ≫
   [⊢ f ≫ f- ⇐ String]
   --------
   [⊢ (v:#%app v:image f-) ⇒ Producer]]
  [(_ f #:length n:exact-nonnegative-integer) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:image f- #:length n-) ⇒ (Producer n)]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   #:do [(define len
           (with-handlers ([exn? (λ _ #f)])
             (eval (syntax->datum #'n) (make-base-namespace))))]
   --------
   [⊢ (v:#%app v:image f- #:length n-) ⇒ #,(or (and len #`(Producer #,len))
                                               #'Producer)]])

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
  [(_ f #:length n:exact-nonnegative-integer) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:length n-) ⇒ (Producer n)]]
  [(_ f #:length n) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:length n-) ⇒ Producer]]
  [(_ f #:start n:exact-nonnegative-integer
        #:end m:exact-nonnegative-integer) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   [⊢ m ≫ m- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:start n- #:end m-)
      ⇒ (Producer #,(add1 (- (stx->datum #'m)
                             (stx->datum #'n))))]]
  [(_ f #:start n #:end m) ≫
   [⊢ f ≫ f- ⇐ String]
   [⊢ n ≫ n- ⇐ Int]
   [⊢ m ≫ m- ⇐ Int]
   --------
   [⊢ (v:#%app v:clip f- #:start n- #:end m-) ⇒ Producer]])

(define-primop producer-length v:producer-length : (→ Producer Int))

;; playlist combinators -------------------------------------------------------
;; TODO: should be interleaved Transition and Producer?
(define-typed-syntax multitrack
  [(_ (~and p (~not _:keyword)) ... #:length n:exact-nonnegative-integer) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:when (stx-andmap (λ (t) (or (Transition? t) (Producer? t))) #'(ty ...))
   [⊢ n ≫ n- ⇐ Int]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:length n-) ⇒ (Producer n)]]
  [(_ (~and p (~not _:keyword)) ... #:length n) ≫
   [⊢ p ≫ p- ⇒ ty] ...
   #:when (stx-andmap (λ (t) (or (Transition? t) (Producer? t))) #'(ty ...))
   [⊢ n ≫ n- ⇐ Int]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:length n-) ⇒ Producer]]
  [(_ (~and p (~not _:keyword)) ... #:transitions trans) ≫
   [⊢ p ≫ p- ⇒ (~Producer _)] ...
   [⊢ trans ≫ trans- ⇒ (~Listof (~Transition _))]
   ------------
   [⊢ (v:#%app v:multitrack p- ... #:transitions trans-) ⇒ Producer]]
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
      ⇒ #,(mk-type
           #`(Producer-
              #,(apply + (map (λ (x)
                                (define x*
                                  (syntax-parse x
                                    [(_ y) (stx->datum #'y)]))
                                (or (and (number? x*) x*)
                                    +inf.0)) ; TODO: fixme?
                              (attribute n)))))]]
  [(_ p ...) ≫ ; producers only
   [⊢ p ≫ p- ⇒ (~Producer n)] ...
   ------------
   [⊢ (v:#%app v:playlist p- ...)
      ⇒ (Producer-
         #,(apply + (map (λ (m)
                           (define m*
                             (syntax-parse m
                               [(_ mm) (stx->datum #'mm)]))
                           (or (and (number? m*) m*)
                               +inf.0)) ; TODO: fixme
                         (attribute n))))]]
  [(_ p1 p/t ... pn) ≫ ; producers + transitions
   [⊢ p1 ≫ p1- ⇒ (~Producer n1)]
   [⊢ pn ≫ pn- ⇒ (~Producer nn)]
   ;[⊢ p/t ≫ p/t- ⇒ (~or (~Producer n) (~Transition m))] ... ; doesnt work
   [⊢ p/t ≫ p/t- ⇒ P-or-T] ...
   #:with ((~or (~Producer n) (~Transition m)) ...) #'(P-or-T ...)
   ------------
   [⊢ (v:#%app v:playlist p1- p/t- ... pn-)
      ⇒ (Producer-
         #,(- (apply + (map (λ (x)
                              (define x*
                                (syntax-parse x
                                  [(_ y) (stx->datum #'y)]))
                              (or (and (number? x*) x*)
                                  +inf.0)) ; TODO: fixme?
                            (cons #'n1 (cons #'nn (attribute n)))))
              (apply + (map (λ (x)
                              (define x*
                                (syntax-parse x
                                  [(_ y) (stx->datum #'y)]))
                              (or (and (number? x*) x*)
                                  +inf.0)) ; TODO: fixme?
                            (attribute m)))))]]
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
   [⊢ t ≫ t- ⇐ Producer]
   [⊢ b ≫ b- ⇐ Producer]
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
