// ============================================================================
// 03-proof-theory.typ
// Arguments 3 and 4: property modules; the gate across four systems; Option C.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Proof Theory <sec:proof-theory>

This chapter presents the two proof-theoretic arguments. Argument 3 is that the
ascent MPL $arrow.r$ IPL $arrow.r$ CPL is organized around _properties_ ---
typeclasses on a theory --- rather than around connectives. Argument 4 is that a
single such property, `IsIntuitionistic`, is instantiated across four different
proof systems by the _same_ device, and that this is what settles the
long-running definitional controversy in favour of Option C.

== Argument 3: properties, not connectives <sec:properties>

A logic's strength is carried by its _theory_, and strength is added by
typeclasses that assert a theory contains certain schemas.

#definition([The property classes (`Defs.lean:166-180`)])[
  A theory $T$ is _intuitionistic_ if it contains every explosion instance, and
  _classical_ if it contains every double-negation-elimination instance:
  $
    "IsIntuitionistic" T &:= forall A, (bot arrow.r A) in T \
    "IsClassical" T &:= forall A, (not not A arrow.r A) in T
  $
  Each class is characterized by a set inclusion (`Defs.lean:169-171`,
  `:179-180`):
  $
    "IsIntuitionistic" T arrow.l.r "IPL" subset.eq T
    quad quad
    "IsClassical" T arrow.l.r "CPL" subset.eq T
  $
]

Two features make this genuinely modular rather than cosmetic. First, the
properties are _additive_: extending a theory preserves them
(`instIsIntuitionisticExtension`, `Defs.lean:190-191`; and the classical
analogue at `:195-196`), each proved in one line by `grind`. Adding axioms never
destroys explosion. Second, the base $"MPL" := emptyset$ (`Defs.lean:154`)
admits _no_ `IsIntuitionistic` instance, because `IsIntuitionistic` $emptyset$
would require $"IPL" subset.eq emptyset$, which is false. Explosion is therefore
_structurally unconstructible_ at MPL strength, not merely unproved.

=== The semantic mirror

The same modularity appears on the semantic side as a pair of _mixins on an
element_, not typeclasses on the algebra (`BotProperties.lean:88-159`):

#definition([Least and initial bottom (`BotProperties.lean:92-100, 149-159`)])[
  For a designated element $b$ of an ordered algebra $H$:
  $
    "HasLeastBot" b &:= forall a, b ale a \
    "HasInitialBot" b &:= forall a, b ale a quad ("as the unique arrow" b arrow.r a)
  $
  with `instHasInitialBotOfHasLeastBot` giving `HasLeastBot` $arrow.r$
  `HasInitialBot` automatically.
]

The source is careful about status here, and so are we: `HasLeastBot` is
_"a `Prop`-valued predicate on a specific element $b : H$, not a typeclass on
the type $H$"_ (`BotProperties.lean:61-64`). This is exactly what lets the
semantic hierarchy avoid duplicating the `IsIntuitionistic` machinery --- the
one evaluator's `bot_val` parameter is retained; only a predicate on it changes.
The "initial object" reading of `HasInitialBot` is the code's own gloss of the
inequality $b ale a$ (`BotProperties.lean:31-36`); as always
(@sec:cat-caveat), no `CategoryTheory` machinery is invoked --- it is an
order-theoretic fact wearing categorical clothing.

== Argument 4: one gate, four systems <sec:gate>

The MPL $arrow.r$ IPL step is a _single_ architectural move --- adjoin explosion
as a constructor carrying an `[IsIntuitionistic T]` instance binder --- and it is
made, verbatim in spirit, in four different proof systems.

#figure(
  table(
    columns: (auto, auto, auto, auto),
    stroke: none,
    align: left,
    table.hline(),
    table.header(
      [*System*], [*MPL base*], [*Gated $bot$-rule*], [*Available at*],
    ),
    table.hline(),
    [Hilbert],
    [`MinPropAxiom` (8 ctors)],
    [`efq` in `IntPropAxiom`; `peirce` in `PropositionalAxiom`],
    [IPL / CPL],

    [Natural deduction],
    [10 ungated rules],
    [`efq` #h(0.3em) `[IsIntuitionistic T]` (`Basic.lean:182-183`)],
    [IPL / CPL],

    [Sequent (LJ)],
    [structural rules],
    [`botL` #h(0.3em) `[IsIntuitionistic T]` (`LJ/Basic.lean:98-100`)],
    [IPL / CPL],

    [Curry--Howard],
    [term formers],
    [`efq` #h(0.3em) `[IsIntuitionistic T]` (`CurryHoward/Defs.lean:102-103`)],
    [IPL / CPL],
    table.hline(),
  ),
  caption: [One gate, `[IsIntuitionistic T]`, instantiated four times. The
    Hilbert substrate `MinPropAxiom` has 8 connective schemas; `IntPropAxiom`
    adds `efq` (`Axioms.lean:126-150 / 89-116`); `PropositionalAxiom` adds
    `peirce` (`:48-78`).],
)

In every case, because the gated rule carries `[IsIntuitionistic T]` and
$"MPL" = emptyset$ admits no such instance, the rule is structurally absent at
the base. The four systems share _one_ formula type (@sec:syntax), so this is
literally the same property doing the same job four times.

=== The controversy and its Option-C resolution

The definitional controversy is whether, once $bot$ is primitive, `efq` should
be an _unconditional_ constructor (call this Option B) rather than a gated one
(Option C). The strongest form of the case for B is Thomas Waring's
(@sec:debate): a constructor with no rule looks unmotivated. The resolution is
_not_ aesthetic. It turns on the metatheory.

#remark("Why Option C, precisely")[
  Splitting natural deduction into a _physically_ $bot$-rule-free inductive for
  MPL (Option B) forces a parallel split of the Curry--Howard term type and a
  re-cut of the subformula / normalization theorem --- the one genuinely hard
  result that task 398 closed. Option C keeps a single inductive, so _one_
  metatheory proof (subformula property, normalization) serves all three
  strengths at once. The gate _is_ the property module: `IsIntuitionistic` is a
  `Prop`-class equal to $"IPL" subset.eq T$, additive under extension.
]

Crucially, "MPL is $bot$-rule-free" is not merely a claim about a naming
abbreviation; it is a _structural_ predicate on derivations
(`NaturalDeduction/Basic.lean:223-235`):

#definition([`IsBotRuleFree` (`NaturalDeduction/Basic.lean:223-235`)])[
  `IsBotRuleFree` is defined by structural recursion over a derivation,
  returning $top$ (or the conjunction of its subderivations' values) on every
  constructor _except_ `efq`, where it returns $bot$ --- the final arm is
  literally `| efq _ => False`. Every `MinimalDerivation` (a `Derivation` for
  $T = "MPL"$) satisfies it, because no `efq` term is constructible at MPL
  strength.
]

#remark("A stale document, corrected")[
  An earlier design note recorded `IsBotRuleFree d : Prop := True`
  (`specs/407_.../mpl-base-design-note.md:42`). That is _not_ what the code
  says. The live definition is the structural recursion above, ending in
  `efq _ => False`; it is a real predicate, not a vacuous constant. This report
  cites the code (`NaturalDeduction/Basic.lean:223-235`) and never the stale
  note.
]

=== Graded faithfulness

Structure-first is not uniform across the four systems, and the report is
explicit about the grading.

- *Hilbert is purest.* `MinPropAxiom` genuinely has no $bot$-rule as a base
  predicate: explosion is a distinct axiom set, not a gated constructor sharing
  an inductive.
- *ND and sequent are structure-first up to the gate.* The `efq` / `botL`
  constructor is _lexically present_ in the one shared inductive; it is inert at
  MPL only because its instance binder cannot be satisfied. Every induction over
  minimal derivations still carries a vacuous `efq` case to discharge.
- *LK's `botL` is ungated* (`SequentCalculus/LK/Basic.lean:76`). This is a
  deliberate, defensible exception: LK is the classical, multi-conclusion
  calculus, so gating $bot$-on-the-left there buys nothing --- classicality is
  already assumed.

=== Option B is deferred, not dismissed

Option B has genuine residual value: a _physically_ $bot$-rule-free derivation
object would give a cleaner setting for minimal-ND normalization and an
abort-free $lambda$-calculus. It is explicitly deferred, not rejected: the task
407 decision record states _"Option C (confirm default) [...] option B stays
deferred to task 409"_ (`decisions.md:5-6`), and the task 407 reports
consistently describe Option B as a literal $bot$-rule-free _inductive_ that
would require re-cutting the subformula proof. The report treats it as live
future work.
