#lang scheme
(require redex)

(provide define-example-definer)

(define-syntax-rule (define-example-definer define-example 
                      mini wrap parser)
  (begin

    (...
     (define-metafunction mini
       as-syntax : any -> val
       [(as-syntax nam) (Stx (Sym nam) •)]
       [(as-syntax number) (Stx number •)]
       [(as-syntax prim) (Stx prim •)]
       [(as-syntax tprim) (Stx tprim •)]
       [(as-syntax (any ...)) (Stx (List (as-syntax any) ...) •)]))

    (define-syntax-rule (define-example id form expected)
      (begin
        (define id
          (lambda (mode)
            (let ([t (wrap (term (as-syntax form)))])
              (case mode
                [(expand) t]
                [(parse) (term (parser ,t))]
                [else (error 'example "unknown mode: ~e" mode)]))))
        (test-equal (id 'parse) (term expected))))))
