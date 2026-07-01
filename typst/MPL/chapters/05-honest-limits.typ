// ============================================================================
// 05-honest-limits.typ
// The honesty ledger (O1-O5) and added caveats, styled on 06-notes.typ.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Honest Limits <sec:honest-limits>

A report that only advocated would not be worth much. This chapter states, as
plainly as possible, what the structure-first design does _not_ establish, what
it costs, and where the community discussion actually landed. It follows the
"Design Choices" pattern: the competing designs are stated as definitions, a
comparison table lays them side by side, and a closing remark lists the
trade-offs the design accepts.

== The competing designs

#definition("Design A --- bot as a primitive nullary operation (implemented)")[
  The signature is the fixed set $sig$ with $bot$ a nullary constructor of
  `Proposition`. Explosion is a _property_ (`IsIntuitionistic`), gating `efq`.
  One formula type, one substitution monad, one evaluator serve MPL / IPL / CPL.
]

#definition("Design B1 --- a bot-free fragment language for MPL")[
  MPL uses a language _without_ $bot$; IPL is obtained by _extending the
  language_ to add $bot$. This changes the similarity type between rungs: the
  MPL formulas are not a subalgebra of the IPL formulas under one signature, and
  the single substitution monad is forfeited.
]

#definition("Design B2 --- bot as a distinguished atom")[
  $bot$ is encoded as a designated atom, $bot : "Atom"$ (the pre-407 state).
  The formula type is shared, but $bot$ is now a _generator_, so substitution
  may send $bot |-> sigma(bot)$; the free/initial universal property fails and
  an $sigma(bot) = bot$ side condition reappears throughout.
]

#figure(
  table(
    columns: (auto, auto, auto, auto),
    stroke: none,
    align: left,
    table.hline(),
    table.header(
      [*Property*], [*Design A*], [*Design B1*], [*Design B2*],
    ),
    table.hline(),
    [One signature across rungs], [Yes], [No (language grows)], [Yes],
    [$bot$ fixed by substitution], [Yes (`| bot => .bot`)], [n/a], [No ($bot |-> sigma bot$)],
    [Single substitution monad], [Yes], [No], [Broken universal property],
    [Leastness is a variety identity], [Yes ($bot inter x = bot$)], [No], [No ($bot$ not a signature constant)],
    [Conventional textbook norm], [No (minority)], [Common], [Common],
    table.hline(),
  ),
  caption: [The three designs compared. Design A is a deliberate _minority_
    choice; Designs B1/B2 are closer to the usual textbook and formalization
    conventions.],
)

== The honesty ledger

#remark("O1")[
  *The substitution argument is pragmatic, not decisive.*
  The free-monad / substitution-invariance argument (@sec:syntax) does not by
  itself _select_ the signature: declaring $bot$ a generator also yields a free
  monad, so the universal property restates the choice rather than forcing it.
  The honest form is pragmatic --- _given_ the goal of one shared substitution
  monad across MPL / IPL / CPL (and the downstream modal, temporal, bimodal
  logics), treating $bot$ as an operation removes the $sigma(bot) = bot$ side
  condition. The genuinely decisive structural argument is the keystone
  KF6 (@sec:kf6), not substitution-invariance.
]

#remark("O2")[
  *An unconstrained $bot$ at MPL carries a cost.*
  That $bot$ is totally unconstrained at MPL is literally true (no `MinPropAxiom`
  mentions $bot$; `bot_val` is a free parameter; $top := bot arrow.r bot$
  imposes nothing; `efq` is unconstructible). The cost is the flip side: MPL
  proves _vacuous_ well-typed $bot$-theorems --- e.g. the `implyK` instance at
  $bot$ --- so at MPL strength $bot$ behaves like an ordinary atom. This is the
  double edge that fuels O1.
]

#remark("O3")[
  *The sorry-free scope is exactly the Hilbert / algebraic layer.*
  Sorry-free: the derivability subsumption chain (`ConservativeChain.lean:152`)
  and GHA / HA / BA algebraic completeness
  (`HilbertCompleteness.lean:64, 93, 122, 155`); the
  $"Derivable MinPropAxiom" phi.alt arrow.l.r "GHAValid" phi.alt$
  correspondence is exact, with no fragment caveat. _Not_ clean: the
  tableau / decidability layer carries live task-317 sorries (Minimal and
  Intuitionistic tableau completeness; the registered MPL/IPL decision instances
  carry `sorryAx`), and the fully generic fragment-lift is _open_ (task 410).
  The clean-proof claim is scoped to the Hilbert and algebraic development only.
]

#remark("O4")[
  *"Property module" is partly a re-description.*
  `efq` is a _lexical constructor_ of the one shared derivation inductive, and
  `MinimalDerivation` is an _abbreviation_, not a physically $bot$-rule-free type
  (that is deferred to task 409). Every induction over minimal derivations still
  carries a vacuous `efq` case to discharge. The structural predicate that makes
  "$bot$-rule-free" precise is `IsBotRuleFree` (`NaturalDeduction/Basic.lean:223-235`,
  ending `efq _ => False`) --- and note again that the earlier design note's
  `IsBotRuleFree := True` (`mpl-base-design-note.md:42`) is stale; the code, not
  the note, is authoritative.
]

#remark("O5")[
  *The downstream payoff is a bet, not a delivery.*
  The claimed strategic benefit --- MPL as a reusable intuitionistic substrate
  for the modal / temporal / bimodal logics --- is not realized today. Those
  embeddings are currently CPL-only (Łukasiewicz), so the minimal / intuitionistic
  structure is erased at the embedding boundary (task 415), and the
  shared-metatheory substrate was judged NO-GO (task 448). Structure-first
  _front-loads the scaffolding_ (gated-`efq` and `bot_forces` templates, a green
  morphism substrate) for an eventual intuitionistic lift, but this is an unpaid
  bet the design is _positioned_ to win, not a benefit already banked.
]

== Two further caveats

#remark("No LawfulMonad, no formalized Adjunction")[
  The free-monad and reflector / faithful-functor language used throughout is an
  _informal_ reading of order-theoretic facts. There is no `LawfulMonad
  Proposition` instance and no `CategoryTheory.Functor` / `Adjunction` instance
  anywhere in `Cslib/Logics/Propositional/` (verified: zero search hits). The
  order-theoretic facts glossed by this language are real, sorry-free theorems;
  the categorical framing is a description, not a proved universal property.
]

#remark("The Zulip thread parked Design A")[
  The community discussion did not ratify Design A. The final message
  (#606970606) was an unanswered compromise proposal from the design's most
  substantive critic --- to postpone minimal logic and take IPL as the base for
  now. The design is defended here on its technical merits, not on a consensus
  that was not reached. Per the AI policy raised in that thread
  (#605827029 / #605840135), any upstream-facing prose must be human-authored;
  this report is an internal artifact.
]

#remark("Precise algebraic naming")[
  The MPL algebra tier is a _pointed generalized-Heyting (Johansson) algebra_ ---
  a GHA with a designated constant $bot$ --- not a bare GHA. Mathlib's
  generalized Heyting algebra has $top$ but no $bot$; the designated $bot$ is
  exactly what the structure-first design adds, and it is what makes the
  leastness identity (@sec:kf6) statable in the first place.
]

== Trade-offs accepted

#remark("Trade-offs Accepted")[
  The structure-first design accepts:
  + *A pragmatic, not apodictic, core argument.* Substitution-invariance is a
    convenience of the signature choice (O1); the load-bearing argument is the
    subvariety keystone (KF6).
  + *Vacuous $bot$-theorems at MPL.* $bot$ behaves like an atom at the base
    (O2), the price of leaving it genuinely unconstrained there.
  + *A bounded clean-proof claim.* Only the Hilbert / algebraic layer is
    sorry-free (O3); tableau decidability (task 317) and generic fragment-lift
    (task 410) are open.
  + *A minority convention.* Designs B1 / B2 are the more common textbook norm;
    Design A is chosen deliberately for the cross-system goal, not because it is
    standard.
  + *An unbanked downstream bet.* The modal / temporal payoff is positioning,
    not delivery (O5).

  These are acceptable because the cross-system architecture --- one signature,
  one substitution monad, one evaluator, one metatheory serving four proof
  systems and a whole tower of logics --- is a real, verified economy today, and
  the subvariety framing it enables (KF6) is well-formed _only_ under this
  design.
]
