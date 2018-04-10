#lang racket
;(require (for-syntax syntax/parse))

  (let-syntax
;      ([tmp (dynamic-require "2-colorfade.rkt" 'vid-ty2)])
      ([tmp (dynamic-require "newcolorfade.rkt" 0)])
    4)
  #;(local-expand
      #'(let-syntax
;            ([tmp (dynamic-require "newcolorfade.rkt" 'x)])
            ([tmp (dynamic-require "2-colorfade.rkt" 'vid-ty2)])
          4)
      'expression null)

