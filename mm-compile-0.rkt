#lang racket
(require redex
         "rewrites.rkt"
         "define-example.rkt"
         slideshow/pict)

;; based on mm-stxcase.rkt

;; Added phases, sequence of environments, run-time environments.
;; Change expand+parse to compile.

(define-language mini

  ;; Executable AST and values:
  [ast var (App ast ast ...) (Fun var ast) (Const val)]
  [var (Var nam)]
  [val (Clo (Fun var ast) rtenv) atom (List val ...) stx]

  ;; Syntax objects (a subset of values):
  [stx (Stx atom ctx) (Stx (List stx ...) ctx)]
  [id (Stx sym ctx)]
  [ctx • (Mark ctx mrk) (Rename ctx id nam phase)]
  [phase natural]

  ;; Literal values:
  [atom sym prim desc-other-atom] ; `desc-other-atom' typesets as "...."
  [desc-other-atom number]
  [sym (Sym nam)]
  [prim SE MKS desc-other-prim] ; `desc-other-prim' typesets as "...."
  [desc-other-prim + - CONS CAR CDR LIST]

  ;; Expand-time environment & run-time environment:
  [env desc-env] ; `desc-env' typesets as prose
  [desc-env ((nam transform) ...)]
  [rtenv desc-rtenv]
  [desc-rtenv ((nam val) ...)]
  [transform TFun TLetSyntax TLetForSyntax TLetSyntaxForSyntax TQuote TSyntax (TVar nam) val]

  ;; Env-pairs
  [envpairs ((EP env rtenv) ...)]

  ;; Use names for vars, addrs, and marks
  [(nam) desc-name] ; `desc-name' typesets as prose
  [mrk nam]
  [desc-name variable-not-otherwise-mentioned]

  ;; For name generation:
  [gen (number ...)]
  [env+gen (Fst env gen)])

;; ----------------------------------------
;; Generic metafunctions that typeset as set operations:

(define-metafunction mini
  [(is-in? any_1 ()) #f]
  [(is-in? any_1 (any_1 any_2 ...)) #t]
  [(is-in? any_1 (any_2 any_3 ...)) (is-in? any_1 (any_3 ...))])

(define-metafunction mini
  [(emptyset) ()])

(define-metafunction mini
  [(add-elem any_1 any_2) (any_1 . any_2)])

(define-metafunction mini
  [(same? any_1 any_2) ,(equal? (term any_1) (term any_2))])

;; ----------------------------------------
;; Implementation of primitives:

(define-metafunction mini
  [(plus number_1 number_2) ,(+ (term number_1) (term number_2))])
(define-metafunction mini
  [(minus number_1 number_2) ,(- (term number_1) (term number_2))])

(define-metafunction mini
  δ/stx : prim (val ...) -> val
  [(δ/stx SE ((Stx val ctx))) val]
  [(δ/stx MKS (atom (Stx val ctx))) (Stx atom ctx)]
  [(δ/stx MKS ((List stx ...) (Stx val ctx))) (Stx (List stx ...) ctx)])

(define-metafunction/extension δ/stx mini
  δ : prim (val ...) -> val
  [(δ + (number_1 number_2)) (plus number_1 number_2)]
  [(δ - (number_1 number_2)) (minus number_1 number_2)]
  [(δ CONS (val_1 (List val_2 ...))) (List val_1 val_2 ...)]
  [(δ CAR ((List val_1 val_2 ...))) val_1]
  [(δ CDR ((List val_1 val_2 ...))) (List val_2 ...)]
  [(δ LIST (val ...)) (List val ...)])

;; ----------------------------------------
;; Evaluating AST:

(define-metafunction mini
  eval : ast rtenv -> val
  [(eval (Var nam) rtenv)
   (rtlookup rtenv nam)]
  [(eval (App ast_op ast_arg ...) rtenv)
   (app val_op (val_arg ...))
   (where val_op (eval ast_op rtenv))
   (where (val_arg ...) ((eval ast_arg rtenv) ...))]
  [(eval (Fun var ast_body) rtenv)
   (Clo (Fun var ast_body) rtenv)]
  [(eval (Const val) rtenv) val])

(define-metafunction mini
  app : val (val ...) -> val
  [(app (Clo (Fun (Var nam) ast_body) rtenv) (val_arg))
   (eval ast_body (rtextend rtenv nam val_arg))]
  [(app prim (val_arg ...))
   (δ prim (val_arg ...))])

;; ----------------------------------------
;; Syntax-object operations:

(define-metafunction mini
  ;; Adds or cancels a mark
  addremove : mrk (mrk ...) -> (mrk ...)
  [(addremove mrk_1 (mrk_1 mrk_2 ...)) (mrk_2 ...)]
  [(addremove mrk_1 (mrk_2 ...)) (mrk_1 mrk_2 ...)])

(define-metafunction mini
  ;; Extracts all marks in order, removing cancelling pairs
  marksof : id nam -> (mrk ...)
  [(marksof (Stx sym •) nam) ()]
  [(marksof (Stx sym (Mark ctx mrk)) nam)
   (addremove mrk (mrk_2 ...))
   (where (mrk_2 ...) (marksof (Stx sym ctx) nam))]
  [(marksof (Stx sym (Rename ctx id_2 nam phase)) nam) ()]
  [(marksof (Stx sym (Rename ctx id_2 nam_2 phase)) nam) 
   (marksof (Stx sym ctx) nam)])

(define-metafunction mini
  ;; Resolves an identifier to a name; this is the heart of
  ;;  the syntax-object support for lexical scope
  resolve : id phase -> nam
  [(resolve (Stx (Sym nam) •) phase) nam]
  [(resolve (Stx (Sym nam) (Mark ctx mrk)) phase)
   (resolve (Stx (Sym nam) ctx) phase)]
  [(resolve (Stx (Sym nam) (Rename ctx id nam_new phase)) phase)
   nam_new
   (where nam_1 (resolve id phase))
   (where nam_1 (resolve (Stx (Sym nam) ctx) phase))
   (side-condition (term (same? (marksof id nam_1) (marksof (Stx (Sym nam) ctx) nam_1))))]
  [(resolve (Stx (Sym nam) (Rename ctx id nam_2 phase_2)) phase)
   (resolve (Stx (Sym nam) ctx) phase)])

(define-metafunction mini
  rename : stx id nam phase -> stx
  ;; Simply pushes `Rename's down through a syntax object
  [(rename (Stx atom ctx) id nam phase)
   (Stx atom (Rename ctx id nam phase))]
  [(rename (Stx (List stx ...) ctx) id nam phase) 
   (Stx (List (rename stx id nam phase) ...)
        (Rename ctx id nam phase))])

(define-metafunction mini
  mark : stx mrk -> stx
  ;; Simply pushes `Mark's down through a syntax object
  [(mark (Stx atom ctx) mrk) 
   (Stx atom (Mark ctx mrk))]
  [(mark (Stx (List stx ...) ctx) mrk) 
   (Stx (List (mark stx mrk) ...) 
        (Mark ctx mrk))])

(define-metafunction mini
  strip : stx -> val
  ;; Recursively strips lexical context from a syntax object
  [(strip (Stx atom ctx))
   atom]
  [(strip (Stx (List stx ...) ctx)) 
   (List (strip stx) ...)])

;; ----------------------------------------
;; Expand-time environment operations:

(define-metafunction mini
  lookup : env nam -> transform
  [(lookup ((nam transform) any_2 ...) nam) transform]
  [(lookup (any_1 any_2 ...) nam) (lookup (any_2 ...) nam)])

(define-metafunction mini
  extend : env nam transform -> env
  [(extend env nam transform) ((nam transform) . env)])

(define-metafunction mini
  extend* : env ((nam transform) ...) -> env
  [(extend* env ((nam transform) ...)) ((nam transform) ... . env)])

(define-metafunction mini
  rtlookup : rtenv nam -> val
  [(rtlookup ((nam val) any_2 ...) nam) val]
  [(rtlookup (any_1 any_2 ...) nam) (rtlookup (any_2 ...) nam)])

(define-metafunction mini
  rtextend : rtenv nam val -> rtenv
  [(rtextend rtenv nam val) ((nam val) . rtenv)])

;; ----------------------------------------
;; Fresh-name helper for expander:

(define-metafunction mini
  [(fresh-name (Stx (Sym nam) ctx) gen)
   ,(string->symbol (format "~a~a"
                            (term nam)
                            (apply
                             string-append
                             (for/list ([c (reverse (term gen))])
                               (format ":~a" c)))))])

(define-metafunction mini
  [(enumerate number) ()]
  [(enumerate number stx stx_2 ...)
   ,(cons (term number)
          (term (enumerate ,(add1 (term number)) stx_2 ...)))])

(define-metafunction mini
  [(phaseup phase any)
   ,(+ (term phase) (term any))])

;; ----------------------------------------
;; The expander:

(define-metafunction mini
  compile : stx phase env+gen envpairs -> ast

  ;; lambda (0)
  [(compile (Stx (List id_lam id_arg stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Fun (Var nam_new) ast_body)
   (where TFun (lookup env_0 (resolve id_lam phase)))
   (where nam_new (fresh-name id_arg gen))
   (where env_0* (extend env_0 nam_new (TVar nam_new)))
   (where ast_body (compile (rename stx_body id_arg nam_new phase) phase [Fst env_0* (0 . gen)] ((EP env_1 rtenv_1) ...)))]

  ;; quote (1) & syntax (2)
  [(compile (Stx (List id_quote stx) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Const (strip stx))
   (where TQuote (lookup env_0 (resolve id_quote phase)))]
  [(compile (Stx (List id_syntax stx) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Const stx)
   (where TSyntax (lookup env_0 (resolve id_syntax phase)))]

  ;; reference (3)
  [(compile id phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Var nam)
   (where (TVar nam) (lookup env_0 (resolve id phase)))]

  ;; let-syntax (4)
  [(compile (Stx (List id_ls id stx_rhs stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...))
   ast_body
   (where TLetSyntax (lookup env_0 (resolve id_ls phase)))
   (where nam_new (fresh-name id gen))
   (where env_0* (extend env_0 nam_new (eval (compile stx_rhs (phaseup phase 1) [Fst env_1 (0 . gen)] ((EP env_2 rtenv_2) ...)) rtenv_1)))
   (where ast_body (compile (rename stx_body id nam_new phase) phase [Fst env_0* (1 . gen)] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...)))]

  ;; macro invocation (5)
  [(compile stx_macapp phase [Fst env_0 gen] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...))
   ast
   (where (Stx (List id_mac stx_arg ...) ctx) stx_macapp)
   (where val (lookup env_0 (resolve id_mac phase)))
   (where mrk_new (fresh-name (Stx (Sym mrk) •) gen))
   (where stx_exp (app val ((mark stx_macapp mrk_new))))
   (where ast (compile (mark stx_exp mrk_new) phase [Fst env_0 (0 . gen)] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...)))]

  ;; let-for-syntax (6)
  [(compile (Stx (List id_lfs id stx_rhs stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...))
   ast_body
   (where TLetForSyntax (lookup env_0 (resolve id_lfs phase)))
   (where nam_new (fresh-name id gen))
   (where env_1* (extend env_1 nam_new (TVar nam_new)))
   (where rtenv_1* (extend rtenv_1 nam_new (eval (compile stx_rhs (phaseup phase 1) [Fst env_1 (0 . gen)] ((EP env_2 rtenv_2) ...)) rtenv_1)))
   (where ast_body (compile (rename stx_body id nam_new (phaseup phase 1)) phase [Fst env_0 (1 . gen)] ((EP env_1* rtenv_1*) (EP env_2 rtenv_2) ...)))]

  ;; let-syntax-for-syntax (7)
  [(compile (Stx (List id_lsfs id stx_rhs stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) (EP env_3 rtenv_3) ...))
   ast_body
   (where TLetSyntaxForSyntax (lookup env_0 (resolve id_lsfs phase)))
   (where nam_new (fresh-name id gen))
   (where env_1* (extend env_1 nam_new (eval (compile stx_rhs (phaseup phase 2) [Fst env_2 (0 . gen)] ((EP env_3 rtenv_3) ...)) rtenv_2)))
   (where ast_body (compile (rename stx_body id nam_new (phaseup phase 1)) phase [Fst env_0 (1 . gen)] ((EP env_1* rtenv_1) (EP env_2 rtenv_2) (EP env_3 rtenv_3) ...)))]

  ;; application (8)
  [(compile (Stx (List stx_rator stx_rand ...) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (App (compile stx_rator phase [Fst env_0 (0 . gen)] ((EP env_1 rtenv_1) ...))
        (compile stx_rand phase [Fst env_0 (number . gen)] ((EP env_1 rtenv_1) ...)) ...)
   (where/hidden (number ...) (enumerate 1 stx_rand ...))]
  )

;; ----------------------------------------
;; Helpers for writing examples:

(define-metafunction mini
  preamble-env : -> env
  [(preamble-env) ((lambda TFun)
                   (let-syntax TLetSyntax)
                   (let-for-syntax TLetForSyntax)
                   (let-syntax-for-syntax TLetSyntaxForSyntax)
                   (quote TQuote)
                   (syntax TSyntax))])

(define (preamble-env-pict)
  (define-metafunction mini
    preamble-env : -> env
    [(preamble-env) ((lambda TFun)
                     (let-syntax TLetSyntax)
                     (let-for-syntax TLetForSyntax)
                     (let-syntax-for-syntax TLetSyntaxForSyntax)
                     (Quote TQuote)
                     (syntax TSyntax))])
  (with-rewrites
   (lambda ()
     (metafunction->pict preamble-env))))

(define-metafunction mini
  [(identity ast) ast])

;; ----------------------------------------
;; Examples:

(define-example-definer define-example
  mini 
  (lambda (t) (term (compile ,t 0 [Fst (preamble-env) ()] ((EP (preamble-env) ()) (EP (preamble-env) ())))))
  identity)

(define-example simple-macro-example
  (let-syntax x (lambda z (syntax (quote 2))) (x 1))
  (Const 2))

(define-example reftrans-macro-example
  (lambda z (let-syntax x (lambda s (syntax z)) (lambda z (x))))
  (Fun (Var z) (Fun (Var z:0:1) (Var z))))

(define-example hyg-macro-example
  (lambda z (let-syntax x (lambda s 
                            ('MKS
                             ('LIST (syntax lambda)
                                    (syntax z)
                                    ('CAR ('CDR ('SE s))))
                             (syntax here)))
              (x z)))
  (Fun (Var z) (Fun (Var z:0:1:0) (Var z))))

;; some variations on hyg-macro-example using let-for-syntax
;; extract lambda stx from x macro into helper var
(define-example hyg2-macro-example
  (lambda z
    (let-for-syntax lam-stx (syntax lambda)
      (let-syntax x (lambda s 
                      ('MKS
                       ('LIST lam-stx
                              (syntax z)
                              ('CAR ('CDR ('SE s))))
                       (syntax here)))
        (x z))))
  (Fun (Var z) (Fun (Var z:0:1:1:0) (Var z))))

;; create transformer-maker to implement x macro
(define-example hyg3-macro-example
  (lambda z
    (let-for-syntax lam-stx (syntax lambda)
      (let-for-syntax x-tx (lambda kw-stx
                             (lambda s 
                               ('MKS
                                ('LIST kw-stx
                                       (syntax z)
                                       ('CAR ('CDR ('SE s))))
                                (syntax here))))
        (let-syntax x (x-tx lam-stx)
          (x z)))))
  (Fun (Var z) (Fun (Var z:0:1:1:1:0) (Var z))))

;; uses same transformer-maker, but given 'LIST prim instead of lambda
(define-example hyg4-macro-example
  (lambda z
    (let-for-syntax lam-stx (syntax lambda)
      (let-for-syntax x-tx (lambda kw-stx
                             (lambda s 
                               ('MKS
                                ('LIST kw-stx
                                       (syntax z)
                                       ('CAR ('CDR ('SE s))))
                                (syntax here))))
        (let-syntax x (x-tx (syntax 'LIST))
          (x z)))))
  (Fun (Var z) (App (Const LIST) (Var z) (Var z))))

;; let-syntax-for-syntax
(define-example lsfs-example
  (lambda z
    (let-syntax-for-syntax syntax-here
                           (lambda s
                             ('MKS
                              ('LIST (syntax 'MKS)
                                     ('CAR ('CDR ('SE s)))
                                     ('MKS ('LIST (syntax syntax)
                                                  s)
                                           (syntax here)))
                              (syntax here)))
      (let-syntax x (lambda xs
                      (syntax-here
                       ('LIST (syntax lambda)
                              (syntax z)
                              ('CAR ('CDR ('SE xs))))))
        (x z))))
  (Fun (Var z) (Fun (Var z:0:1:1:0) (Var z))))

(define-example thunk-example
  (let-syntax 
      thunk (lambda e
              ('MKS
               ('LIST (syntax lambda) 
                      (syntax a) 
                      ('CAR ('CDR ('SE e))))
               e))
    (((lambda a (thunk ('+ a '1))) '5) '0))
  (App (App (Fun (Var a:1:0:0) (Fun (Var a:1:0:0:0:0) (App (Const +) (Var a:1:0:0) (Const 1))))
            (Const 5))
       (Const 0)))

;; ----------------------------------------
;; Typesetting:

(define (lang->pict)
  (with-rewrites
   (lambda ()
     (vl-append
      10
      (language->pict mini #:nts '(ast var val))
      (language->pict mini #:nts '(stx id ctx phase))
      (language->pict mini #:nts '(atom sym prim))
      (language->pict mini #:nts '(env rtenv nam mrk transform))))))

(define (eval->pict)
  (with-rewrites
   (lambda ()
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions])
       (vl-append
        10
        (metafunction->pict eval)
        (metafunction->pict app)
        ;;(metafunctions->pict δ δ/stx)
        )))))

(define (metas->pict)
  (with-rewrites
   (lambda ()
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions])
       (vl-append
        10
        (metafunction->pict resolve)
        )))))

(define (expand*->pict cases)
  (with-rewrites
   (lambda ()
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions]
                    [metafunction-cases cases])
       (metafunction->pict compile)))))

(define (base-expand->pict) (expand*->pict '(0 1 2 3 8)))
(define (macro-expand->pict) (expand*->pict '(4 5)))
(define (lfs-expand->pict) (expand*->pict '(6)))
(define (lsfs-expand->pict) (expand*->pict '(7)))

(provide mini
         lang->pict
         eval->pict
         metas->pict
         base-expand->pict
         macro-expand->pict
         lfs-expand->pict
         lsfs-expand->pict
         preamble-env-pict)
