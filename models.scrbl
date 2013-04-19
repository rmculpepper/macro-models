#lang scribble/manual
@(require redex/pict
          "rewrites.rkt")

@;{

Each section starts with a @(require ....) form that imports the
pict-makers from the corresponding model. See that file for the Redex
code. The typesetting/styling is in "rewrites.rkt".

}

@(define-syntax-rule (mm->pict e)
   (parameterize ((default-font-size 10)
                  (metafunction-font-size 10)
                  (label-font-size 10))
     (with-rewrites (lambda () (term->pict mglet:mini e)))))

@; ------------------------------------------------------------
@(require (prefix-in mbase: "mm-stxcase-fixes.rkt"))

@section{Hygienic Macros}

We start with the basic model of hygienic macros from @emph{Macros
That Work Together}---that is, without the extensions the paper
introduces. There are separate @tt{parse} and @tt{expand}
functions. Since we have no phases, @racket[let-syntax] right-hand
sides are not expanded, only parsed.

@(mbase:lang->pict)

@(mbase:eval->pict)

@(mbase:metas1->pict)

@(mbase:metas2->pict)

@(mbase:expand->pict)

@; ------------------------------------------------------------
@(require (prefix-in mphase: "mm-compile-0.rkt"))

@section{... With Phases}

The following model adds phases and run-time environments.
@mm->pict[(Rename ...)] wraps are phase-specific: binding a name at
one phase does not shadow bindings at other phases.

@(mphase:lang->pict)

Evaluation uses run-time environments and closures instead of
substitution:

@(mphase:eval->pict)

The @mm->pict[resolve] function is phase-specific:

@(mphase:metas->pict)

A single @mm->pict[compile] function replaces @mm->pict[parse] and
@mm->pict[expand]. Compilation takes a syntactic environment
(@mm->pict[env]) and a sequence (infinite in principle, finite for
simplicity of the model) of pairs of syntactic and run-time
environments (@mm->pict[(EP env rtenv)]).

@(mphase:base-expand->pict)

Macro transformers are compiled and evaluated using the environments
of the next phase.

@(mphase:macro-expand->pict)

Variable bindings can be added to the next phase using the
@racket[let-for-syntax] form.

@(mphase:lfs-expand->pict)

Here's a @racket[let-syntax-for-syntax] form, which binds macros in
the next phase (the macro transformers are compiled and evaluated
using the environments two phase levels up).

@(mphase:lsfs-expand->pict)

The initial syntactic environment @emph{(at each phase)} is

@(mphase:preamble-env-pict)

@; ------------------------------------------------------------
@(require (prefix-in mglet: "mm-compile-1.rkt"))

@section{... With Generalized @tt{let}}

The following changes to the previous model generalize
@racket[let-syntax] and @racket[let-for-syntax] to @racket[letS] and
@racket[letV], which take the phase to bind in as an argument.

Examples using @racket[let-syntax] etc should be rewritten as follows:

@racketblock[
(let-syntax x e1 e2)            => (letS 0 x e1 e2)
(let-for-syntax x e1 e2)        => (letV 1 x e1 e2)
(let-syntax-for-syntax x e1 e2) => (letS 1 x e1 e2)
]

The set of transformers is updated:

@(mglet:lang->pict)

The @mm->pict[TLetSyntax], @mm->pict[TLetForSyntax], and
@mm->pict[TLetSyntaxForSyntax] rules of @mm->pict[compile] are
replaced with the following:

@(mglet:expand->pict)

The initial syntactic environment (at each phase) is

@(mglet:preamble-env-pict)

The following helper metafunction is added:

@(mglet:metas->pict)

@; ------------------------------------------------------------

@;{
@(require (prefix-in mglet2: "mm-compile.rkt"))

@section{... With Generalized @tt{let}, refactored}

@(mglet2:expand->pict)

The following helper metafunctions are added:

@(mglet2:metas->pict)

}
