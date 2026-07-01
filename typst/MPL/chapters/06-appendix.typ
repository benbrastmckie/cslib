// ============================================================================
// 06-appendix.typ
// Table of every Lean source anchor cited in the report.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Appendix: Source Anchors <sec:appendix>

Every Lean anchor cited in this report, for a reader who wants to jump straight
to source. Paths are relative to `Cslib/Logics/Propositional/`. Line ranges were
verified against live source (task 464 research round 2).

#figure(
  table(
    columns: (auto, auto, auto),
    stroke: none,
    align: left,
    table.hline(),
    table.header(
      [*File : lines*], [*Declaration*], [*Supports*],
    ),
    table.hline(),
    [`Defs.lean:81-92`], [`Proposition` inductive], [Arg 1 (5 primitives, $bot$ nullary)],
    [`Defs.lean:95-102`], [`neg` / `top` / `iff`], [Arg 1 (derived operators)],
    [`Defs.lean:128-134`], [`Proposition.subst`], [Arg 1 (`| bot => .bot` at :131)],
    [`Defs.lean:136-139`], [`Monad Proposition`], [Arg 1 (no `LawfulMonad`)],
    [`Defs.lean:154-158`], [`MPL` / `IPL` abbrevs], [Arg 3 ($"MPL" = emptyset$)],
    [`Defs.lean:166-171`], [`IsIntuitionistic`, `isIntuitionisticIff`], [Arg 3 ($arrow.l.r "IPL" subset.eq T$)],
    [`Defs.lean:175-180`], [`IsClassical`, `isClassicalIff`], [Arg 3],
    [`Defs.lean:190-196`], [extension instances], [Arg 3 (additivity)],
    [`Defs.lean:198-206`], [`intuitionisticCompletion`], [Arg 3],
    [`ProofSystem/Axioms.lean:48-78`], [`PropositionalAxiom` (adds `peirce`)], [Arg 4 (CPL)],
    [`ProofSystem/Axioms.lean:89-116`], [`IntPropAxiom` (adds `efq`)], [Arg 4 (IPL)],
    [`ProofSystem/Axioms.lean:126-150`], [`MinPropAxiom` (8 ctors)], [Arg 4 (MPL base)],
    [`NaturalDeduction/Basic.lean:44-115`], [module docstring], [Arg 1 / 4 (Design A argument)],
    [`NaturalDeduction/Basic.lean:182-183`], [gated `efq`], [Arg 4 (`[IsIntuitionistic T]`)],
    [`NaturalDeduction/Basic.lean:223-235`], [`IsBotRuleFree` (structural)], [Arg 4 (`efq _ => False`)],
    [`NaturalDeduction/Basic.lean:242-243`], [`MinimalDerivation` abbrev], [Arg 4 / O4],
    [`NaturalDeduction/Basic.lean:392-408`], [`substAtom` (`efq` arm :408)], [Arg 1 (side-condition-free)],
    [`SequentCalculus/LJ/Basic.lean:98-100`], [gated `botL`], [Arg 4 (IPL)],
    [`SequentCalculus/LK/Basic.lean:76`], [ungated `botL`], [Arg 4 (classical exception)],
    [`CurryHoward/Defs.lean:102-103`], [gated `efq`], [Arg 4 (term calculus)],
    [`Semantics/Algebra.lean:94-100`], [`AlgEvaluate`, `bot_val`], [Arg 5 (`| .bot => bot_val` :97)],
    [`Semantics/Kripke.lean:81-98`], [`IForces`, `IForces_bot`], [Arg 5 (`bot_forces` :95-98)],
    [`Semantics/Algebra/BotProperties.lean:31-36`], [initial-object framing], [Arg 5 (informal caveat)],
    [`Semantics/Algebra/BotProperties.lean:61-64`], [mixin-on-element note], [Arg 3],
    [`Semantics/Algebra/BotProperties.lean:92-100`], [`HasLeastBot`], [Arg 3 / 5],
    [`Semantics/Algebra/BotProperties.lean:149-159`], [`HasInitialBot`], [Arg 3 / 5],
    [`Semantics/Algebra/ConservativeChain.lean:152`], [`derivability_subsumption_chain`], [Arg 6],
    [`Semantics/Algebra/ConservativeChain.lean:226,246,270`], [fragment ladder theorems], [Arg 6],
    [`Semantics/Algebra/MplConservativeChain.lean:197,231,263`], [MPL-side biconditionals], [Arg 6 (#606397657)],
    [`Semantics/Algebra/HilbertCompleteness.lean:64,93,122,155`], [completeness + 3 corollaries], [Arg 6],
    [`Semantics/Algebra/FragmentGeneric.lean:174`], [`ghaValid_iff_haValid_of_botFree`], [Arg 6],
    table.hline(),
  ),
  caption: [Verified Lean source anchors cited in this report.],
)

== Zulip message index

The debate (@sec:debate) cites the following messages from the CSLib Zulip
"Propositional Logic" thread. Identifiers are given for internal traceability;
any upstream-facing use of this material must be human-authored (AI policy,
#605827029 / #605840135).

#figure(
  table(
    columns: (auto, auto, auto),
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
    [#605827029 / #605840135], [Henson / Brast-McKie], [AI-policy challenge and reply],
    [#605862751], [Brast-McKie], [`ipl_conservative_over_mpl` delivered],
    [#606026592], [Doty], [suggests fragment-chain extension],
    [#606128428], [Brast-McKie], [fragment chain delivered],
    [#606397657], [Brast-McKie], [MPL-side conservativity mirror],
    [#606970606], [Waring], [ND-symmetry objection + "postpone MPL" (unanswered)],
    table.hline(),
  ),
  caption: [Cited Zulip messages (internal reference only).],
)
