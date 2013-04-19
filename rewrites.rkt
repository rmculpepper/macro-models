#lang racket/base
(require redex
         unstable/gui/redex
         slideshow/pict
         racket/class
         racket/gui/base
         racket/list)

(provide with-rewrites
         ->ps 
         grammar+reductions
         append-steps
         step-...
         explain
         together
         prim ast trans langle rangle)

(default-font-size 9)
(metafunction-font-size 9)
(label-font-size 9)

(define (prim s) (text s '(bold . modern) (default-font-size)))
(define (ast s) (text s '(bold caps . roman) (default-font-size)))
(define (trans s) (text s '(caps . roman) (default-font-size)))
(define (lit s) (text s (literal-style) (default-font-size)))
(define (atag s) (trans s))

(define transform (text "transform" (non-terminal-style) (default-font-size)))
(define value (text "val" (non-terminal-style) (default-font-size)))

(define (between s a b)
  (build-lw s
            (lw-line a)
            0
            (+ (lw-column a) (lw-column-span a))
            (max 0 (- (lw-column b)
                      (+ (lw-column a) (lw-column-span a))))))

(define (re-lw new-e lw)
  (build-lw new-e
            (lw-line lw) (lw-line-span lw)
            (lw-column lw) (lw-column-span lw)))

(define (refit orig new)
  (append (list (between "" (just-before "" (car orig)) (car new)))
          new
          (list (between "" (just-after "" (last new)) (just-after "" (last orig))))))

(define (<-) (let-values ([(h w d a) (send (dc-for-text-size) get-text-extent "m")])
               (dc (lambda (dc x y)
                     (let ([p (send dc get-pen)])
                       (send dc set-pen (send p get-color) 0.5 'solid)
                       (let ([m (+ y (/ h 2))]
                             [x (+ 2 x)]
                             [w (- w 4)])
                         (send dc draw-line x m (+ x w) m)
                         (send dc draw-line x m (+ x (/ w 4)) (- m (/ w 4)))
                         (send dc draw-line x m (+ x (/ w 4)) (+ m (/ w 4))))
                       (send dc set-pen p)))
                   w h (- h d) d)))

(define (=>) "→")

(define (mapsto) " ↦ ")

#|
(define (=>) (let-values ([(h w d a) (send (dc-for-text-size) get-text-extent "m")])
               (dc (lambda (dc x y)
                     (let ([p (send dc get-pen)])
                       (send dc set-pen (send p get-color) 0.5 'solid)
                       (let ([m (+ y (/ h 2))]
                             [x (- (+ x w) 2)]
                             [w (- w 4)])
                         (send dc draw-line x m (- x w) m)
                         (send dc draw-line x m (- x (/ w 4)) (- m (/ w 4)))
                         (send dc draw-line x m (- x (/ w 4)) (+ m (/ w 4))))
                       (send dc set-pen p)))
                   w h (- h d) d)))
|#

(define (make-subst-rewrite pre <- post)
  (lambda (lws)
    (refit
     lws
     (list (list-ref lws 2)
           (between pre
                    (list-ref lws 2)
                    (list-ref lws 3))
           (list-ref lws 3)
           (between (<-)
                    (list-ref lws 3)
                    (list-ref lws 4))
           (list-ref lws 4)
           (just-after post (list-ref lws 4))))))

(define subst-rewrite (make-subst-rewrite "[" #|<-|# mapsto "]"))
(define extend-rewrite (make-subst-rewrite "+{" #|=>|# mapsto "}"))

(define (make-subst*-rewrite pre <- post1 post2)
  (lambda (lws)
    (let* ([subs (lw-e (list-ref lws 3))]
           [subs2 (lw-e (list-ref subs 1))])
      (refit
       lws
       (list (list-ref lws 2)
             (between pre
                      (list-ref lws 2)
                      (list-ref lws 3))
             (re-lw "" (list-ref subs 0))
             (re-lw "" (list-ref subs2 0))
             (list-ref subs2 1)
             (between (=>)
                      (list-ref subs2 1)
                      (list-ref subs2 2))
             (list-ref subs2 2)
             (re-lw post1 (list-ref subs2 3))
             (list-ref subs 2)
             (re-lw "" (list-ref subs 3))
             (just-after post2 (list-ref lws 3)))))))

(define subst*-rewrite (make-subst*-rewrite "[" <- "" "]"))
(define extend*-rewrite (make-subst*-rewrite "+{" <- "}" ""))
(define store*-rewrite (make-subst*-rewrite "{" <- "" "}"))

(define (seq-at lw . cs)
  (build-lw (map (lambda (c) (just-before c lw)) cs)
            (lw-line lw) 0
            (lw-column lw) 0))

(define (fix-subscript p)
  (let ([p (symbol->string p)])
    (hbl-append (text (substring p 0 1) (non-terminal-style) (default-font-size))
                (text (substring p 2) (non-terminal-subscript-style) (default-font-size)))))

(define (store-rewrite lws)
  (let* ([re-sig (seq-at (list-ref lws 4)
                         (fix-subscript (lw-e (list-ref lws 2)))
                         "("
                         (lw-e (list-ref lws 3))
                         ")")]
         [sub (extend-rewrite (list re-sig ; fake "("
                                    re-sig ; fake "subst"
                                    re-sig
                                    (list-ref lws 4)
                                    (list-ref lws 5)))])
    (extend-rewrite (list (list-ref lws 0)
                          (list-ref lws 1)
                          (list-ref lws 2)
                          (list-ref lws 3)
                          (build-lw sub
                                    (lw-line (car sub)) 0
                                    (lw-column (car sub))
                                    (- (+ (lw-column (last sub))
                                          (lw-column-span (last sub)))
                                       (lw-column (car sub))))))))

(define (alloc-rewrite lws)
  (extend-rewrite (list (list-ref lws 0)
                        (list-ref lws 1)
                        (list-ref lws 2)
                        (list-ref lws 3)
                        (just-after "∅" (list-ref lws 3))
                        (list-ref lws 4))))
  
(define (taller s)
  (define p (text s (default-style) (default-font-size)))
  (define h (pict-height p))
  (drop-below-ascent (scale (launder p) 1 1.3) (* 0.1 h)))

(define (langle [taller? #t]) ((if taller? taller values) "\u2329"))
(define (rangle [taller? #t]) ((if taller? taller values) "\u232A"))

(define (angle-brackets who lws #:taller? [taller? #t])
  (if (= (length lws) 3)
      (list (re-lw (langle taller?) (car lws))
            (re-lw (atag who) (cadr lws))
            (re-lw (rangle taller?) (caddr lws)))
      (refit
       lws
       (let* ([open (re-lw (langle taller?) (car lws))]
              [prev-tag (cadr lws)]
              [lws (drop (drop-right lws 1) 2)])
         (append (if who
                     (list open
                           (between "" open prev-tag)
                           (re-lw (atag who) prev-tag))
                     (list open (between "" open (car lws))))
                 (if who
                     lws
                     (append
                      (list (car lws)
                            (just-after "," (car lws))
                            (cadr lws))
                      (if (null? (cddr lws))
                          null
                          (list (just-after "," (cadr lws))
                                (caddr lws)))))
                 (list (just-after (rangle taller?) (last lws))))))))

#;
(define (symbol lws)
  (refit
   lws
   (let ([e (caddr lws)]
         [/ (text "/" 'roman (default-font-size))])
     (list (just-before / e)
           e
           (just-after / e)))))

(define (symbol lws)
  (refit
   lws
   (let ([e (caddr lws)]
         [quot (text "\u2019" 'roman (default-font-size))])
     (list (just-before quot e)
           e))))

(define (binary sep lws)
  (refit 
   lws
   (list
    (list-ref lws 2)
    (just-after sep (list-ref lws 2))
    (between "" (list-ref lws 2) (list-ref lws 3))
    (list-ref lws 3))))

(define (delta name lws)
  (refit lws
         (list* (re-lw name (list-ref lws 1))
                (between "(" (list-ref lws 1) (list-ref lws 2))
                (list-ref lws 2)
                (between ", " (list-ref lws 2) (cadr (lw-e (list-ref lws 3))))
                (comma-ize (cdr (lw-e (list-ref lws 3)))))))

(define (constructor name)
  (lambda (lws)
    (refit lws
           (list* (re-lw name (list-ref lws 1))
                  (between "(" (list-ref lws 1) (list-ref lws 2))
                  (comma-ize (cddr lws))))))

(define (comma-ize lws)
  (let loop ([lws lws])
    (cond
     [(or (null? (cdr lws))
          (null? (cddr lws)))
      lws]
     [(positive? (lw-line-span (car lws)))
      ;; a line break?
      (cons (car lws) (loop (cdr lws)))]
     [else
      (list*
       (car lws)
       (between ", " (car lws) (cadr lws))
       (loop (cdr lws)))])))
  
(define bm-dc #f)

(define (name)
  (text "name" (non-terminal-style) (default-font-size)))
(define (var)
  (text "var" (non-terminal-style) (default-font-size)))

(define (rng lws)
  (refit lws
         (list (re-lw "rng" (list-ref lws 1))
               (between "(" (list-ref lws 1) (list-ref lws 2))
               (list-ref lws 2)
               (just-after ")" (list-ref lws 2)))))

(define (with-rewrites thunk)
  (parameterize (#|
                 [metafunction-pict-style 'left-right/compact-side-conditions]
                 [literal-style 'modern]
                 [white-bracket-sizing (let ([orig (white-bracket-sizing)])
                                         (lambda (str size)
                                           (let-values ([(a b c d) (orig str size)])
                                             (define (less v [n 1]) (max (- v n) 0))
                                             (if (string=? str "[")
                                                 (values (less a 2) b c (less d))
                                                 (values a (less b 2) (less c) d)))))]
                 [dc-for-text-size (or (dc-for-text-size)
                                       bm-dc
                                       (begin
                                         (set! bm-dc (make-object bitmap-dc% (make-object bitmap% 1 1)))
                                         bm-dc))]
                 |#)
    (with-atomic-rewriter*
     (lambda ()
       (with-compound-rewriter*
        (lambda ()
          (with-unquote-rewriter
           (lambda (lw)
             (if (and (pair? (lw-e lw))
                      (pair? (cdr (lw-e lw)))
                      (lw? (cadr (lw-e lw)))
                      (eq? (lw-e (cadr  (lw-e lw))) 'filter))
                 (re-lw
                  (htl-append (text "{" 'roman (default-font-size))
                              (var)
                              (=>)
                              transform
                              (text " | " 'roman (default-font-size))
                              (vl-append
                               (hbl-append
                                (text "\u03BE" 'default (default-font-size))
                                (text "(" 'roman (default-font-size))
                                (var)
                                (text ") = " 'roman (default-font-size))
                                transform)
                               (hb-append
                                (text " and " 'roman (default-font-size))
                                transform
                                (text " ≠ " 'roman (default-font-size))
                                (trans "Stop")
                                (text "}" 'roman (default-font-size)))))
                  lw)
                 lw))
           (thunk)))
        (list
         'preamble-env (lambda (lws) (refit lws (list (re-lw "ξ₀" (cadr lws))))) ;; FIXME: env_init
         'plus (lambda (lws) (binary "+" lws))
         'minus (lambda (lws) (binary "\u2212" lws))
         'and? (lambda (lws) (binary " and " lws))
         'same? (lambda (lws) (binary " = " lws))
         'is-in? (lambda (lws) (binary " \u2208 " lws))
         'greater? (lambda (lws) (binary " > " lws))
         'binds? (lambda (lws) (list (list-ref lws 2) 
                                     (just-after "  binds" (list-ref lws 2))
                                     (list-ref lws 3)))
         'elem (lambda (lws) (refit lws (drop-right (drop lws 2) 1)))
         'emptyset (lambda (lws) (refit lws (list (re-lw "∅" (list-ref lws 0)))))
         'add-elem (lambda (lws)
                     (refit lws
                            (list (just-before "{" (list-ref lws 2))
                                  (list-ref lws 2)
                                  (just-after "}∪" (list-ref lws 2))
                                  (between "" (list-ref lws 2) (list-ref lws 3))
                                  (list-ref lws 3))))                                  
         'lookup (lambda (lws) 
                   (refit
                    lws
                    (append
                     (list (list-ref lws 2) 
                           (between "(" (list-ref lws 2) (list-ref lws 3))
                           (list-ref lws 3)
                           (just-after ")" (list-ref lws 3)))
                     (if ((length lws) . > . 5)
                         ;; Has store
                         (list (just-after (text "Σ" `(subscript . roman) (default-font-size)) (list-ref lws 3)))
                         null))))
         'rtlookup (lambda (lws) 
                     (refit
                      lws
                      (list (list-ref lws 2) 
                            (between "(" (list-ref lws 2) (list-ref lws 3))
                            (list-ref lws 3)
                            (just-after ")" (list-ref lws 3)))))
         'Fst (lambda (lws) 
                (refit lws (list (caddr lws))))
         'addremove (lambda (lws) (binary " ⊕ " lws))
         'extend extend-rewrite
         'rtextend extend-rewrite
         'extend* extend*-rewrite
         'subst subst-rewrite
         'store store-rewrite
         'alloc alloc-rewrite
         'store-lookup (lambda (lws)
                         (refit
                          lws
                          (list
                           (list-ref lws 2)
                           (between "(" (list-ref lws 2) (list-ref lws 3))
                           (list-ref lws 3)
                           (just-after ")" (list-ref lws 3)))))
         'store-val (lambda (lws)
                      (store*-rewrite (list* (car lws)
                                             (cadr lws)
                                             (just-after "" (cadr lws))
                                             (cddr lws))))
         'rng rng
         'fresh-name (lambda (lws)
                       (refit lws 
                              (list (re-lw "fresh" (car lws)))))
         'EP (lambda (lws) (angle-brackets #f lws #:taller? #f))
         'St (lambda (lws) (angle-brackets #f lws))
         'StE (lambda (lws) (angle-brackets #f lws))
         'Sym (lambda (lws) (symbol lws))
         'Exp (lambda (lws) (angle-brackets "Exp" lws))
         'Eval (lambda (lws) (angle-brackets "Eval" lws))
         'Local-Exp (lambda (lws) (angle-brackets "Local" lws))
         'Def-Exp (lambda (lws) (angle-brackets "Defs-Exp" lws))
         'InExp (lambda (lws) (angle-brackets "InExp" lws))
         'InBind (lambda (lws) (angle-brackets "InBind" lws))
         'InIntDef (lambda (lws) (angle-brackets "InDef" lws))
         'Plain (lambda (lws) (refit lws (drop-right (cddr lws) 1)))
         'phaseup (lambda (lws)
                    (refit lws
                      (let ([arg1 (third lws)]
                            [arg2 (fourth lws)])
                        (list arg1 (between "+" arg1 arg2) arg2))))
         'Set (lambda (lws) 
                (refit
                 lws
                 (let ([lws (refit lws (drop-right (cddr lws) 1))])
                   (append (list (just-before "{" (car lws)))
                           lws
                           (list (just-after "}" (last lws)))))))
         'Bind (lambda (lws)
                 (refit lws
                        (let ([lws (refit lws (drop-right (cddr lws) 1))])
                          (list (cadr lws)
                                (<-)
                                (caddr lws)))))
         'Comma (lambda (lws) (refit 
                               lws
                               (let ([lws (drop-right (cddr lws) 1)])
                                 (append lws
                                         (list (just-after "," (last lws)))))))
         'δ (lambda (lws) (delta "δ" lws))
         'δ/stx (lambda (lws) (delta "δ" lws))
         'App (constructor (ast "App"))
         'Const (constructor (ast "Const"))
         'Let (constructor (ast "Let"))
         'Ref (constructor (ast "Ref"))
         'Fun (constructor (ast "Fun"))
         'Clo (constructor (ast "Clo"))
         'Var (constructor (ast "Var"))
         'Letrec (constructor (ast "Letrec"))
         'Atom (constructor (ast "Atom"))
         'List (constructor (ast "List"))
         'Stx (constructor (ast "Stx"))
         'Namespace (constructor (trans "Namespace"))
         'Mark (constructor (trans "Mark"))
         'Rename (constructor (trans "Rename"))
         'Defs (constructor (trans "Defs")))))
      (list
       'Quote (lambda () (text "quote" (literal-style) (default-font-size)))
       'nam name
       '• (lambda () (text "•" 'default (default-font-size))) ;; tt bullet is too small
       'Σ (lambda () (text "Σ" (default-style) (default-font-size)))
       'δ (lambda () (text "δ" (default-style) (default-font-size)))
       'kont (lambda () (text "κ" 'default (default-font-size)))
       'env (lambda () (text "\u03BE" (default-style) (default-font-size)))
       'rtenv (lambda () (text "σ" (default-style) (default-font-size)))
       'phase (lambda () (text "p" (non-terminal-style) (default-font-size)))
       '.... (lambda () (text "...." 'default (default-font-size)))
       'SPC (lambda () (text " " 'default (default-font-size)))
       'all-tprim (lambda () (text "tprim" (non-terminal-style) (default-font-size)))
       'pre-ctx (lambda () (text "ctx" (non-terminal-style) (default-font-size)))
       'pre-val (lambda () (text "val" (non-terminal-style) (default-font-size)))
       'desc-other-prim (lambda () (text "...." 'roman (default-font-size)))
       'desc-other-val (lambda () (text "...." 'roman (default-font-size)))
       'desc-other-atom (lambda () (text "...." 'roman (default-font-size)))
       'desc-other-trans (lambda () (text "...." 'roman (default-font-size)))
       'desc-old-mixture (lambda () (text "...." 'roman (default-font-size)))
       'desc-old-F (lambda () (text "...." 'roman (default-font-size)))
       'desc-old-tprim (lambda () (text "...." 'roman (default-font-size)))
       'desc-name (lambda () (hbl-append (text "a token such as " 'roman (default-font-size))
                                         (lit "x")
                                         (text ", " 'roman (default-font-size))
                                         (lit "egg")
                                         (text ", or " 'roman (default-font-size))
                                         (lit "lambda")))
       'desc-env (lambda () (hbl-append (text "a mapping from " 'roman (default-font-size))
                                        (name)
                                        (text " to " 'roman (default-font-size))
                                        transform))
       'desc-rtenv (lambda () (hbl-append (text "a mapping from " 'roman (default-font-size))
                                          (name)
                                          (text " to " 'roman (default-font-size))
                                          value))
       'desc-Σ (lambda () (hbl-append (text "definition-context store, " 'roman (default-font-size))
                                      (text "σ" (non-terminal-style) (default-font-size))
                                      (text " " 'roman (default-font-size))
                                      (=>)
                                      (text " (" 'roman (default-font-size))
                                      (text "id" (non-terminal-style) (default-font-size))
                                      (text " " 'roman (default-font-size))
                                      (=>)
                                      (text " " 'roman (default-font-size))
                                      (text "sym" (non-terminal-style) (default-font-size))
                                      (text ")" 'roman (default-font-size))))
       'desc-S (lambda () (hbl-append (text "set of " 'roman (default-font-size))
                                      (text "σ" (non-terminal-style) (default-font-size))))
       'CONS (lambda () (prim "cons"))
       'CAR (lambda () (prim "car"))
       'CDR (lambda () (prim "cdr"))
       'SEL (lambda () (prim "sel"))
       'LIST (lambda () (prim "list"))
       'SE (lambda () (prim "stx-e"))
       'MKS (lambda () (prim "mk-stx"))
       'LOCAL-VALUE (lambda () (prim "lvalue"))
       'LOCAL-EXPAND (lambda () (prim "lexpand"))
       'NEW-DEFS (lambda () (prim "new-defs"))
       'DEF-BIND (lambda () (prim "def-bind"))
       '+ (lambda () (prim "+"))
       '- (lambda () (prim "-"))
       'NULL (lambda () (trans "null"))
       'OpNS (lambda () (trans "OpNS"))
       'ArgNS (lambda () (trans "ArgNS"))
       'TFun (lambda () (trans "Fun"))
       'TLet (lambda () (trans "Let"))
       'TLetV (lambda () (trans "Let-Value-at-Phase"))
       'TLetS (lambda () (trans "Let-Syntax-at-Phase"))
       'TGLet (lambda () (trans "GenLet"))
       'TFLet (lambda () (trans "FLet"))
       'TLetrec (lambda () (trans "Letrec"))
       'TQuote (lambda () (trans "Quote"))
       'TSyntax (lambda () (trans "Syntax"))
       'TLetSyntax (lambda () (trans "Let-Syntax"))
       'TLetForSyntax (lambda () (trans "Let-For-Syntax"))
       'TLetSyntaxForSyntax (lambda () (trans "Let-Syntax-For-Syntax"))
       'TStop (lambda () (trans "Stop"))
       'TVar (lambda () (trans "Var"))))))

(define (with-atomic-rewriter* thunk l)
  (if (null? l)
      (thunk)
      (with-atomic-rewriter
       (car l) (cadr l)
       (with-atomic-rewriter* thunk (cddr l)))))

(define (with-compound-rewriter* thunk l)
  (if (null? l)
      (thunk)
      (with-compound-rewriter
       (car l) (cadr l)
       (with-compound-rewriter* thunk (cddr l)))))


(define (->ps file mk)
    (let ([pss (current-ps-setup)])
      (send pss set-mode 'file)
      (send pss set-file file)
      (let ([dc (make-object post-script-dc% #f)])
        (let ([p (parameterize ([dc-for-text-size dc]) (mk))])
          (send dc start-doc "pict")
          (send dc start-page)
          (draw-pict p dc 0 0)
          (send dc end-page)
          (send dc end-doc)))))

(define (grammar+reductions g r)
  (vc-append 10 g r))

(define (append-steps #:init [init ghost] . l)
  (let ([-> (text "=" 'roman (default-font-size))])
    (apply
     vl-append
     (map (lambda (a b)
            (htl-append 4 
                        (if (pair? b)
                            (lbl-superimpose (ghost a) (car b))
                            a)
                        (if (pair? b)
                            (cdr b)
                            b)))
          (cons (init ->) (map (lambda (x) ->) (cdr l))) 
          l))))

(define-syntax-rule (step-... e ...)
  (explain "..." e ... "..."))

(define (explain . es)
  (apply htl-append 
         (add-between
          (for/list ([e (in-list es)])
            (if (pict? e)
                e
                (text e '(italic . roman) (default-font-size))))
          (text " " '(italic . roman) (default-font-size)))))

(define (together . l)
  ;; Make all pictures the same width to help typesetting
  (let ([w (apply max (map pict-width l))])
    (apply
     values
     (map (lambda (p)
            (lt-superimpose 
             ;; A white frame ensures that the PS bounding
             ;; box is the size we want:
             (colorize (frame (blank w 0)) "white")
             p))
          l))))
