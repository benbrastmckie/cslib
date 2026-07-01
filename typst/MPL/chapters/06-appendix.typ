// ============================================================================
// 06-appendix.typ
// Table of every Lean source anchor cited in the report.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Appendix: Source Anchors <sec:appendix>

Every Lean anchor cited in this report, for a reader who wants to jump straight
to source. Paths are relative to `Cslib/Logics/Propositional/`; entries under
`Algebra/` and `Kripke.lean` are within `Semantics/`. Line ranges were verified
against live source (task 464 research round 2).

#text(size: 9.5pt)[
#figure(
  table(
    columns: (auto, 1fr),
    stroke: none,
    align: (left, left),
    column-gutter: 1em,
    table.hline(),
    table.header(
      [*File : lines*], [*Declaration --- argument supported*],
    ),
    table.hline(),
    [`Defs.lean:81-92`], [`Proposition` inductive --- Arg 1 (5 primitives, $bot$ nullary)],
    [`Defs.lean:95-102`], [`neg` / `top` / `iff` --- Arg 1 (derived operators)],
    [`Defs.lean:128-134`], [`Proposition.subst` --- Arg 1 (`| bot => .bot` at :131)],
    [`Defs.lean:136-139`], [`Monad Proposition` --- Arg 1 (no `LawfulMonad`)],
    [`Defs.lean:154-158`], [`MPL` / `IPL` --- Arg 3 ($"MPL" = emptyset$)],
    [`Defs.lean:166-171`], [`isIntuitionisticIff` --- Arg 3 ($arrow.l.r "IPL" subset.eq T$)],
    [`Defs.lean:175-180`], [`isClassicalIff` --- Arg 3],
    [`Defs.lean:190-196`], [extension instances --- Arg 3 (additivity)],
    [`Defs.lean:198-206`], [`intuitionisticCompletion` --- Arg 3],
    [`ProofSystem/Axioms.lean:48-78`], [`PropositionalAxiom` --- Arg 4 (CPL, adds `peirce`)],
    [`ProofSystem/Axioms.lean:89-116`], [`IntPropAxiom` --- Arg 4 (IPL, adds `efq`)],
    [`ProofSystem/Axioms.lean:126-150`], [`MinPropAxiom` --- Arg 4 (MPL base, 8 ctors)],
    [`NaturalDeduction/Basic.lean:44-115`], [module docstring --- Arg 1 / 4 (Design A argument)],
    [`NaturalDeduction/Basic.lean:182-183`], [gated `efq` --- Arg 4 (`[IsIntuitionistic T]`)],
    [`NaturalDeduction/Basic.lean:223-235`], [`IsBotRuleFree` --- Arg 4 (structural, `efq _ => False`)],
    [`NaturalDeduction/Basic.lean:242-243`], [`MinimalDerivation` --- Arg 4 / O4],
    [`NaturalDeduction/Basic.lean:392-408`], [`substAtom` --- Arg 1 (side-condition-free, :408)],
    [`SequentCalculus/LJ/Basic.lean:98-100`], [gated `botL` --- Arg 4 (IPL)],
    [`SequentCalculus/LK/Basic.lean:76`], [ungated `botL` --- Arg 4 (classical exception)],
    [`CurryHoward/Defs.lean:102-103`], [gated `efq` --- Arg 4 (term calculus)],
    [`Algebra.lean:94-100`], [`AlgEvaluate`, `bot_val` --- Arg 5 (`| .bot => bot_val`, :97)],
    [`Kripke.lean:81-98`], [`IForces`, `IForces_bot` --- Arg 5 (`bot_forces`, :95-98)],
    [`Algebra/BotProperties.lean:31-36`], [initial-object framing --- Arg 5 (informal caveat)],
    [`Algebra/BotProperties.lean:61-64`], [mixin-on-element note --- Arg 3],
    [`Algebra/BotProperties.lean:92-100`], [`HasLeastBot` --- Arg 3 / 5],
    [`Algebra/BotProperties.lean:149-159`], [`HasInitialBot` --- Arg 3 / 5],
    [`Algebra/ConservativeChain.lean:152`], [`derivability_subsumption_chain` --- Arg 6],
    [`Algebra/ConservativeChain.lean:226`], [fragment ladder --- Arg 6 (also :246, :270)],
    [`Algebra/MplConservativeChain.lean:197`], [MPL-side biconditionals --- Arg 6 (also :231, :263; #606397657)],
    [`Algebra/HilbertCompleteness.lean:64`], [completeness theorem --- Arg 6 (corollaries :93, :122, :155)],
    [`Algebra/FragmentGeneric.lean:174`], [`ghaValid_iff_haValid_of_botFree` --- Arg 6],
    table.hline(),
  ),
  caption: [Verified Lean source anchors cited in this report.],
)
]

== Zulip message index

The debate (@sec:debate) cites the following messages from the CSLib Zulip
"Propositional Logic" thread. Identifiers are given for internal traceability;
any upstream-facing use of this material must be human-authored (AI policy,
#605827029 / #605840135).

#figure(
  table(
    columns: (auto, auto, 1fr),
    stroke: none,
    align: left,
    table.hline(),
    table.header([*ID*], [*Sender*], [*Content*]),
    table.hline(),
    [#603163993], [Brast-McKie], [$bot$ simulated via `[Bot Atom]` (pre-407 B2)],
    [#603877853], [Doty], [endorses a separate $bot$ constructor (with Chou)],
    [#603884159], [Waring], [naive $bot |-> bot$ breaks MPL completeness],
    [#604219492], [Brast-McKie], [the decisive substitution / free-algebra post],
    [#605341190], [Waring], [language-first framing (encodings)],
    [#605813681], [Brast-McKie], [$bot$-asymmetry: no intro rule in any system],
    [#605827029 / #605840135], [Henson / B-M], [AI-policy challenge and reply],
    [#605862751], [Brast-McKie], [`ipl_conservative_over_mpl` delivered],
    [#606026592], [Doty], [suggests fragment-chain extension],
    [#606128428], [Brast-McKie], [fragment chain delivered],
    [#606397657], [Brast-McKie], [MPL-side conservativity mirror],
    [#606970606], [Waring], [ND-symmetry objection + "postpone MPL" (unanswered)],
    table.hline(),
  ),
  caption: [Cited Zulip messages (internal reference only).],
)
