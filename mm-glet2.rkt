#lang racket
(require redex
         "rewrites.rkt"
         "define-example.rkt"
         slideshow/pict)

;; based on mm-glet.rkt

;; Refactor binding code into separate metafunctions.

(define-language mini

  ;; Executable AST and values:
  [ast var (App ast ast ...) (Fun var ast) (Const val)]
  [var (Var nam)]
  [val (Clo (Fun var ast) rtenv) atom (List val ...) stx]

  ;; Syntax objects (a subset of values):
  [stx (Stx atom ctx) (Stx (List stx ...) ctx)]
  [id (Stx sym ctx)]
  [ctx • (Mark ctx mrk) (Rename ctx id nam phase)]

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
  [transform TFun TLetV TLetS TQuote TSyntax (TVar nam) val]

  ;; Env-pairs
  [envpairs ((EP env rtenv) ...)]

  ;; Use names for vars, addrs, and marks
  [(nam) desc-name] ; `desc-name' typesets as prose
  [mrk nam]
  [desc-name S V variable-not-otherwise-mentioned]
  [phase integer]

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

(define-metafunction mini
  [(greater? natural_1 natural_2)
   ,(> (term natural_1) (term natural_2))])

(define-metafunction mini
  [(split-at (any ...) 0)
   (EP () (any ...))]
  [(split-at (any_1 any_2 ...) phase)
   (EP (any_1 any_pre ...) (any_post ...))
   (where (EP (any_pre ...) (any_post ...))
          (split-at (any_2 ...) (minus phase 1)))])

;; ----------------------------------------
;; The expander:

(define-metafunction mini
  compile : stx phase env+gen envpairs -> ast

  ;; lambda
  [(compile (Stx (List id_lam id_arg stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Fun (Var nam_new) ast_body)
   (where TFun (lookup env_0 (resolve id_lam phase)))
   (where nam_new (fresh-name id_arg gen))
   (where env_0* (extend env_0 nam_new (TVar nam_new)))
   (where ast_body (compile (rename stx_body id_arg nam_new phase) phase [Fst env_0* (0 . gen)] ((EP env_1 rtenv_1) ...)))]

  ;; quote & syntax
  [(compile (Stx (List id_quote stx) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Const (strip stx))
   (where TQuote (lookup env_0 (resolve id_quote phase)))]
  [(compile (Stx (List id_syntax stx) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Const stx)
   (where TSyntax (lookup env_0 (resolve id_syntax phase)))]

  ;; lets
  [(compile (Stx (List id_lets stx_phase id stx_rhs stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1)  ...))
   ast_body
   (where TLetS (lookup env_0 (resolve id_lets phase)))
   (where phase_let (strip stx_phase))
   (where nam_new (fresh-name id gen))
   (where ((EP env_0* ()) (EP env_1* rtenv_1*) ...)
          (bind-syntax id nam_new phase phase_let stx_rhs [Fst ((EP env_0 ()) (EP env_1 rtenv_1) ...) (0 . gen)]))
   (where ast_body (compile (rename stx_body id nam_new (phaseup phase phase_let)) phase [Fst env_0* (1 . gen)] ((EP env_1* rtenv_1*) ...)))]

  ;; letv
  [(compile (Stx (List id_letv stx_phase id stx_rhs stx_body) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   ast_body
   (where TLetV (lookup env_0 (resolve id_letv phase)))
   (where phase_let (strip stx_phase))
   (side-condition (term (greater? phase_let 0)))
   (where nam_new (fresh-name id gen))
   (where ((EP env_0* ()) (EP env_1* rtenv_1*) ...)
          (bind-value id nam_new phase phase_let stx_rhs [Fst ((EP env_0 ()) (EP env_1 rtenv_1) ...) (0 . gen)]))
   (where ast_body (compile (rename stx_body id nam_new (phaseup phase phase_let)) phase [Fst env_0* (1 . gen)] ((EP env_1* rtenv_1*) ...)))
   ]

  ;; Macro invocation:
  [(compile stx_macapp phase [Fst env_0 gen] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...))
   ast
   (where (Stx (List id_mac stx_arg ...) ctx) stx_macapp)
   (where val (lookup env_0 (resolve id_mac phase)))
   (where mrk_new (fresh-name (Stx (Sym mrk) •) gen))
   (where stx_exp (app val ((mark stx_macapp mrk_new))))
   (where ast (compile (mark stx_exp mrk_new) phase [Fst env_0 (0 . gen)] ((EP env_1 rtenv_1) (EP env_2 rtenv_2) ...)))]

  ;; application
  [(compile (Stx (List stx_rator stx_rand ...) ctx) phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (App (compile stx_rator phase [Fst env_0 (0 . gen)] ((EP env_1 rtenv_1) ...))
        (compile stx_rand phase [Fst env_0 (number . gen)] ((EP env_1 rtenv_1) ...)) ...)
   (where/hidden (number ...) (enumerate 1 stx_rand ...))]

  ;; reference
  [(compile id phase [Fst env_0 gen] ((EP env_1 rtenv_1) ...))
   (Var nam)
   (where (TVar nam) (lookup env_0 (resolve id phase)))])

;; ----

(define-metafunction mini
  bind-syntax : id nam phase phase stx [Fst envpairs gen] -> envpairs
  [(bind-syntax id nam phase phase_let stx [Fst ((EP env rtenv) ...) gen])
   ((EP env_* rtenv_*) ...)
   (where (EP ((EP env_pre rtenv_pre) ...) ((EP env_p rtenv_p) (EP env_p+1 rtenv_p+1) (EP env_p+2 rtenv_p+2) ...))
          (split-at ((EP env rtenv) ...) phase_let))
   (where ast (compile stx (phaseup (phaseup phase phase_let) 1) [Fst env_p+1 gen] ((EP env_p+2 rtenv_p+2) ...)))
   (where env_p* (extend env_p nam (eval ast rtenv_p+1)))
   (where ((EP env_* rtenv_*) ...)
          ((EP env_pre rtenv_pre) ... (EP env_p* rtenv_p) (EP env_p+1 rtenv_p+1) (EP env_p+2 rtenv_p+2) ...))])

(define-metafunction mini
  bind-value : id nam phase phase stx [Fst envpairs gen] -> envpairs
  [(bind-value id nam phase phase_let stx [Fst ((EP env rtenv) ...) gen])
   ((EP env_* rtenv_*) ...)
   (where (EP ((EP env_pre rtenv_pre) ...) ((EP env_p rtenv_p) (EP env_p+1 rtenv_p+1) ...))
          (split-at ((EP env rtenv) ...) phase_let))
   (where ast (compile stx (phaseup phase phase_let) [Fst env_p gen] ((EP env_p+1 rtenv_p+1) ...)))
   (where env_p* (extend env_p nam (TVar nam)))
   (where rtenv_p* (rtextend rtenv_p nam (eval ast rtenv_p)))
   (where ((EP env_* rtenv_*) ...)
          ((EP env_pre rtenv_pre) ... (EP env_p* rtenv_p*) (EP env_p+1 rtenv_p+1) ...))])

;; ----------------------------------------
;; Helpers for writing examples:

(define-metafunction mini
  preamble-env : -> env
  [(preamble-env) ((lambda TFun)
                   (letV TLetV)
                   (letS TLetS)
                   (quote TQuote)
                   (syntax TSyntax))])

(define (preamble-env-pict)
  (define-metafunction mini
    preamble-env : -> env
    [(preamble-env) ((lambda TFun)
                     (letV TLetV)
                     (letS TLetS)
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

;; (current-traced-metafunctions '(resolve lookup strip))

;; (let-syntax x e1 e2)     => (letS 0 x e1 e2)
;; (let-for-syntax x e1 e2) => (letV 1 x e1 e2)

(define-example simple-macro-example
  (letS 0 x (lambda z (syntax (quote 2))) (x 1))
  (Const 2))

(define-example reftrans-macro-example
  (lambda z (letS 0 x (lambda s (syntax z)) (lambda z (x))))
  (Fun (Var z) (Fun (Var z:0:1) (Var z))))

(define-example hyg-macro-example
  (lambda z (letS 0 x (lambda s 
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
    (letV 1 lam-stx (syntax lambda)
      (letS 0 x (lambda s 
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
    (letV 1 lam-stx (syntax lambda)
      (letV 1 x-tx (lambda kw-stx
                     (lambda s 
                       ('MKS
                        ('LIST kw-stx
                               (syntax z)
                               ('CAR ('CDR ('SE s))))
                        (syntax here))))
        (letS 0 x (x-tx lam-stx)
          (x z)))))
  (Fun (Var z) (Fun (Var z:0:1:1:1:0) (Var z))))

;; uses same transformer-maker, but given 'LIST prim instead of lambda
(define-example hyg4-macro-example
  (lambda z
    (letV 1 lam-stx (syntax lambda)
      (letV 1 x-tx (lambda kw-stx
                     (lambda s 
                       ('MKS
                        ('LIST kw-stx
                               (syntax z)
                               ('CAR ('CDR ('SE s))))
                        (syntax here))))
        (letS 0 x (x-tx (syntax 'LIST))
          (x z)))))
  (Fun (Var z) (App (Const LIST) (Var z) (Var z))))

;; let-syntax-for-syntax
(define-example lsfs-example
  (lambda z
    (letS 1 syntax-here (lambda s
                          ('MKS
                           ('LIST (syntax 'MKS)
                                  ('CAR ('CDR ('SE s)))
                                  ('MKS ('LIST (syntax syntax)
                                               s)
                                        (syntax here)))
                           (syntax here)))
      (letS 0 x (lambda xs
                  (syntax-here
                   ('LIST (syntax lambda)
                          (syntax z)
                          ('CAR ('CDR ('SE xs))))))
        (x z))))
  (Fun (Var z) (Fun (Var z:0:1:1:0) (Var z))))

(define-example thunk-example
  (letS 0 thunk (lambda e
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

(define (metas->pict)
  (with-rewrites
   (lambda ()
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions])
       (vl-append
        10
        (metafunction->pict bind-syntax)
        (metafunction->pict bind-value)
        )))))

(define (expand->pict)
  (with-rewrites
   (lambda ()
     (parameterize ([metafunction-pict-style 'left-right/vertical-side-conditions])
       (vl-append
        10
        (parameterize ((metafunction-cases '(3 4)))
          (metafunction->pict compile)))))))

(provide mini
         metas->pict
         expand->pict)
