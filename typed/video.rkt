#lang turnstile
(require (prefix-in v: video))

(define-syntax (provide/types stx)
  (syntax-parse stx
    [(_ . xs)
     #'(begin
         (require (except-in video . xs))
         (provide (all-from-out video))
         (provide . xs))]))

(provide/types blank λ #%app + #%datum define begin)
(provide Producer Int (type-out →) ann)

(begin-for-syntax
  (define old-type-rel (current-typecheck-relation))
  (define (new-type-rel t1 t2)
    (define t1* (stx->datum t1))
    (define t2* (stx->datum t2))
    (or (and (number? t1*) (number? t2*) (<= t1* t2*))
        (old-type-rel t1 t2)))
  (current-type=? new-type-rel)
  (current-typecheck-relation new-type-rel))

; ≫ τ ⊢ ⇒ ⇐
(define-base-type Int)
(define-type-constructor → #:arity > 0)
(define-internal-type-constructor Producer)
(define-syntax (Producer stx)
  (syntax-parse stx
    [_:id ; shorthand for inf length
     (add-orig (mk-type #'(Producer- (v:#%datum . +inf.0))) stx)]
    [(_ n:exact-nonnegative-integer)
     (add-orig (mk-type #'(Producer- n)) stx)]))

(define-typed-syntax #%datum
  [(_ . n:integer) ≫
   --------
   [⊢ (v:#%datum . n) ⇒ Int]]
  [(_ . x) ≫
   --------
   [#:error (type-error #:src #'x #:msg "Unsupported literal: ~v" #'x)]])
   

(define-typed-syntax +
  [_:id ≫ ; HO use is binary
   ----------
   [⊢ v:+ ⇒ (→ Int Int)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Int] ...
   ----------
   [⊢ (v:#%app v:+ e- ...) ⇒ Int]])
   

(define-typed-syntax blank
  [(_ n:exact-nonnegative-integer) ≫
   --------
   [⊢ (v:#%app v:blank n) ⇒ (Producer n)]]
  ;; TODO: use eval when not literal?
  [(_ n) ≫
   --------
   [⊢ (v:#%app v:blank n) ⇒ Producer]])


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
