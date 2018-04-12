#lang racket/base
(require (for-syntax racket/base)
         racket/list
         syntax/parse syntax/stx macrotypes/stx-utils)
(provide (all-defined-out))

;; these stx classes match both lits and expanded (ie, quoted) lits
;; for some reason, (~literal quote) not matching
(define-syntax-class num
  (pattern (~or n:number (_ n:number)) #:attr val #'n))
(define-syntax-class int 
  (pattern (~or n:integer (_ n:integer)) #:attr val #'n))
(define-syntax-class int+others
  (pattern (~and stx ((~or n:int o) ...))
           #:attr vals #'(n.val ...)
           #:attr rest #'(o ...)
           #:attr sum (datum->stx #'stx (stx+ #'vals))))
(define-syntax-class ints
  (pattern (n:int ...) #:attr vals #'(n.val ...)))
(define-syntax-class bool
  (pattern (~or b:boolean (_ b:boolean)) #:attr val #'b))
(define-syntax-class string
  (pattern (~or s:str (_ s:str)) #:attr val #'s))
(define-syntax-class lit
  (pattern (~or x:bool x:int x:num x:string) #:attr val #'x.val))

 ; extract list of quoted numbers
(define stx->num
  (syntax-parser [n:int (stx-e #'n.val)]))
(define (stx->nums stx) (stx-map stx->num stx))
(define (stx->bools stx)
  (stx-map (syntax-parser [n:bool (stx-e #'n.val)]) stx))
(define (stx->datums stx)
  (stx-map (syntax-parser [x:lit (stx-e #'x.val)]) stx))

;; * version also returns stx
(define (stx+ ns)    (apply + (stx->nums ns)))
(define (stxx>= ns)  (datum->stx ns (stx>= (stx->nums ns))))
(define (stxx<= ns)  (datum->stx ns (stx<= (stx->nums ns))))
(define (stx>= ns)   (apply >= (stx->nums ns)))
(define (stx<= ns)   (apply <= (stx->nums ns)))
(define (stx> ns)    (apply > (stx->nums ns)))
(define (stx< ns)    (apply < (stx->nums ns)))
(define (stxx-equal? ns) (datum->stx ns (stx-equal? ns)))
(define (stx-equal? ns) (apply equal? (stx->datums ns)))
(define (stx- ns)    (if (stx-null? ns) 0 (apply - (stx->nums ns))))
(define (stxx/ ns)    (datum->stx ns (stx/ ns)))
(define (stxx-max ns) (datum->stx ns (stx-max ns)))
(define (stxx-min ns) (datum->stx ns (stx-min ns)))
(define (stx/ ns)    (apply quotient (stx->nums ns)))
(define (stx-max ns) (apply max (stx->nums ns)))
(define (stx-min ns) (apply min (stx->nums ns)))

(define stx-e syntax-e)
(define stx? syntax?)
(define fmt format)
(define-syntax stx/loc (make-rename-transformer #'syntax/loc))
(define bound-id=? bound-identifier=?)
(define ++ string-append)
(define num->str number->string)

(define (stx-filter-out-false . stxs)
  (filter
   (λ (xs) (andmap (λ (x) (and x (stx-e x))) xs))
   (apply map list (map stx->list stxs))))

(define (add-stx-props stx ks vs)
  (for/fold ([stx stx]) ([k (in-stx-list ks)]
                         [v (in-stx-list vs)])
    (define k* (string->symbol (stx-e k))) ; must be symbol, to get properly transferred around
    (define v* (stx-e v))
    (syntax-property stx k* v*)))

(define (stx-datum=? x y) (equal? (stx->datum x) (stx->datum y)))

(define (stx-partition p? stx)
  (call-with-values (lambda () (partition p? (stx->list stx))) list))
