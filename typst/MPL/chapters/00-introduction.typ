// ============================================================================
// 00-introduction.typ
// Introduction: thesis, the one-signature picture, and the codebase map.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Introduction

This report makes the case for the *structure-first* design of Minimal
Propositional Logic (MPL) as it is realized in the
`Cslib/Logics/Propositional/` development. The design can be stated in one
sentence: there is a single fixed signature $sig$, and $bot$ is a *designated
but wholly unconstrained nullary operation* of that signature at MPL strength.
Everything else --- the ascent to intuitionistic logic (IPL) and then to
classical logic (CPL) --- is achieved not by changing the language but by
*adding properties* to a theory over that one fixed language.

The competing design, which we call *language-first*, treats MPL as the "real"
base language only once $bot$ has been given its intended meaning (via `efq`),
and recovers weaker logics as *fragments* or *encodings* --- for instance by
modelling $bot$ as a distinguished atom $bot : "Atom"$. The two designs are not
notational variants: they make different choices of *signature*, and that choice
propagates into substitution, into the shape of the proof systems, and into
what can be proved once, generically, versus what must be re-proved per logic.

== Thesis

The thesis of this report has two halves, and we give them equal weight.

*The narrative half.* The type of formulas is the free monad on the signature
$sig$. On this reading $bot$ is a nullary _operation_ --- an element of the free
algebra --- rather than a generator that substitution may replace. The logics

$ "MPL" subset "IPL" subset "CPL" $

then form a _descending chain of varieties_ over that one signature: pointed
generalized-Heyting (Johansson) algebras $supset$ Heyting algebras $supset$
Boolean algebras, each inclusion obtained by adjoining exactly _one_ identity.
The keystone observation --- developed in @sec:syntax and @sec:semantics --- is
that this whole "strengthen-by-a-property $=$ take-a-subvariety" picture is
_only well-formed when $bot$ is a nullary operation_: only then is the defining
condition of IPL, "explosion $=$ leastness", expressible as a variety-defining
_identity_ $bot inter x = bot$. This is what we mean by _modularity around
properties, not connectives_: the object that varies across the tower is the
set of identities a theory satisfies, not the set of connectives its language
provides.

*The engineering half.* The same picture is what makes the Lean development
economical. There is _one_ gate, the typeclass `[IsIntuitionistic T]`, and it
is instantiated across _four_ proof systems --- Hilbert, natural deduction,
sequent calculus, and Curry--Howard terms --- plus a semantic mirror
(`HasLeastBot` / `HasInitialBot`). Because all four systems share one inductive
formula type and one substitution monad, a metatheorem proved once (subformula
property, conservativity, completeness) serves every rung of the tower. The
report is candid about where this economy is graded rather than absolute
(@sec:proof-theory) and about exactly which results are sorry-free
(@sec:honest-limits).

== A note on the categorical language <sec:cat-caveat>

Throughout we use categorical vocabulary --- "free monad", "initial object",
"reflector", "faithful functor" --- because it is the most economical way to
describe the design's shape. The reader should keep in mind, _at every
occurrence_, that this is an _informal reading of order-theoretic facts_. The
`Cslib/Logics/Propositional/` development contains no
`CategoryTheory.Functor` or `CategoryTheory.Adjunction` instance and no
`LawfulMonad` instance (verified by direct search: zero hits). The
order-theoretic facts these phrases gloss --- that $bot$ is fixed by
substitution, that $bot inter x = bot$ characterizes leastness, that the
$bot$-free fragment is preserved under the strengthenings --- are all real,
sorry-free theorems. The categorical language is a description of what the code
_realizes_, never a claim that the code _proves_ a categorical theorem.

== Codebase Structure

The Lean 4 implementation lives in `Cslib/Logics/Propositional/`:

- `Defs.lean` --- the `Proposition` inductive (five primitive constructors,
  with $bot$ nullary), the derived operators $not$ / $top$ / $arrow.l.r$, the
  substitution function `subst` and the `Monad Proposition` instance, and the
  property classes `IsIntuitionistic` / `IsClassical` with their
  characterizations $"IsIntuitionistic" T arrow.l.r "IPL" subset.eq T$.
- `ProofSystem/` --- the Hilbert substrate: the axiom sets `MinPropAxiom`
  (MPL), `IntPropAxiom` (IPL, adds `efq`), and `PropositionalAxiom` (CPL, adds
  `peirce`).
- `NaturalDeduction/` --- the natural-deduction system with the gated `efq`
  constructor, the structural predicate `IsBotRuleFree`, and the
  substitution-invariance witness `substAtom`.
- `SequentCalculus/` --- the intuitionistic sequent calculus `LJ` (with a gated
  `botL`) and the classical `LK` (with an ungated `botL`).
- `CurryHoward/` --- the term calculus with a gated `abort`.
- `Semantics/` --- the algebraic evaluator `AlgEvaluate` (one evaluator for all
  rungs), the $bot$-property mixins `HasLeastBot` / `HasInitialBot`, the Kripke
  forcing relation `IForces`, and the conservativity / completeness metatheory.

The module docstring at `NaturalDeduction/Basic.lean:44-115` states the design
argument in prose, cites the deciding Zulip message (#604219492) by number, and
names the rejected alternatives; it is the source-of-truth for the argument
this report develops, and we quote it directly where it is sharpest.
