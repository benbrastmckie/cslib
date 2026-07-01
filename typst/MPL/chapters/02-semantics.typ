// ============================================================================
// 02-semantics.typ
// Arguments 5 and 6: the bot-ladder on one evaluator; conservativity; KF6.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Semantics <sec:semantics>

The semantic side supplies the keystone argument (Argument 5, in its algebraic
form) and the payoff argument (Argument 6). The keystone is that, over the one
fixed signature, the tower of logics is a _descending chain of varieties_, and
that this framing is available _only_ because $bot$ is a nullary operation.
The payoff is that conservativity between the rungs is then a family of proved,
sorry-free theorems over a single evaluator.

== One evaluator for every rung <sec:evaluator>

There is a single algebraic evaluator, parameterized by a valuation $v$ of atoms
and by _one_ designated value `bot_val` for $bot$ (`Algebra.lean:94-100`):

#definition([The algebraic evaluator (`Algebra.lean:94-100`)])[
  In a generalized Heyting algebra $H$, for $v : "Atom" arrow.r H$ and
  $"bot_val" : H$:
  $
    [| p |] &= v(p) &quad quad [| bot |] &= "bot_val" \
    [| phi.alt arrow.r psi |] &= [| phi.alt |] himp [| psi |]
      &quad quad [| phi.alt and psi |] &= [| phi.alt |] inter [| psi |] \
    [| phi.alt or psi |] &= [| phi.alt |] union [| psi |]
  $
  The $bot$-case is the single line `| .bot => bot_val` (`Algebra.lean:97`).
]

The point to press is that _only the value of `bot_val`, a single element,
changes across the tower_ --- never the evaluator, never the algebra's
operations. This is the semantic content of "one signature, a tower of
properties".

#definition("The bot-ladder")[
  $
    "MPL" &: quad "bot_val" "free (any element of" H")" \
    "IPL" &: quad "bot_val" "least" (bot inter x = bot, "i.e." "HasLeastBot") \
    "CPL" &: quad "bot_val" "least" + "classicality (Boolean" H")"
  $
]

=== Two genuine strengths, not three rungs

It is tempting to read three tiers here --- least bottom, initial bottom, and
the canonical $bot$ of an `OrderBot` --- but that overcounts. There are exactly
_two_ genuine strengths at the $bot$-level (free vs. constrained-least), plus
classicality on top. The three "bottom" notions are _one_ IPL constraint
presented three ways, linked by a single instance-resolution chain:

- `HasLeastBot` --- the order-theoretic form, $forall a, bot ale a$;
- `HasInitialBot` --- the _categorical reading_ of the same inequality as a
  unique arrow $bot arrow.r a$ (`instHasInitialBotOfHasLeastBot`);
- canonical $bot$ from `OrderBot` --- the engineering form, produced for free by
  `instHasLeastBotOrderBot` (`BotProperties.lean:98-100`).

#remark("Informal-categorical reading (mandatory caveat)")[
  Where we call `HasInitialBot` an _initial object_ and read `efq` as _"the
  unique arrow from the initial object"_, this is an informal categorical gloss
  of an order-theoretic fact --- the code's own words are that in a poset _"the
  unique morphism from $b$ to $a$ is the inequality $b ale a$"_
  (`BotProperties.lean:31-36`). No `CategoryTheory.Functor` or `Adjunction`
  instance is invoked anywhere in the propositional development
  (@sec:cat-caveat). Once leastness holds the least element is unique, which is
  precisely why these three presentations collapse to one strength rather than
  three.
]

== The keystone: leastness is an identity (KF6) <sec:kf6>

Here is the argument that the operation-choice does real work, beyond restating
itself. In a generalized Heyting algebra, the order is recovered from the meet,
$b ale a arrow.l.r b inter a = b$, so "bottom is least" becomes the single
_equational_ law

$ bot inter x = bot quad (equiv quad bot himp x = top). $

An _identity_ in the signature $sig$ carves out a _subvariety_. Hence
adjoining leastness takes the variety of pointed generalized-Heyting (Johansson)
algebras down to Heyting algebras; adjoining classicality takes Heyting down to
Boolean. The tower $"MPL" subset "IPL" subset "CPL"$ _is_ a descending chain of
varieties, each step one identity.

#remark("Why this needs bot to be a nullary operation")[
  The law $bot inter x = bot$ is an identity _only if $bot$ is a symbol of the
  signature_. Under the language-first encoding $bot : "Atom"$, the condition
  "$forall p forall a, p ale a$" is not an identity in $sig$ --- $bot$ is now a
  particular _generator_, not a constant of the algebraic language, so
  "leastness of that generator" is not variety-definable. Design A is therefore
  the _unique_ setting in which "explosion $=$ leastness $=$ a subvariety step"
  is even well-formed. This --- not substitution-invariance (@sec:syntax),
  which is a consequence and convenience --- is the decisive structural argument
  for treating $bot$ as a primitive.
]

== A second, independent semantic witness

The Kripke semantics corroborates the same reading without any algebra. Forcing
is parameterized by a predicate `bot_forces` on worlds (`Kripke.lean:81-98`):

#definition([Intuitionistic forcing (`Kripke.lean:81-98`)])[
  $ w tack.r.double bot quad "iff" quad "bot_forces"(w) $
  the single line `IForces_bot` (`Kripke.lean:95-98`). MPL takes an arbitrary
  `bot_forces`; IPL specializes it to $lambda w. "False"$.
]

At MPL strength $bot$'s clause is constrained only by _type_ --- any
world-predicate will do --- which is exactly the forcing-level statement that
$bot$ is unconstrained at the base. That two independent semantics (algebraic
and Kripke) agree on this is evidence that the "unconstrained nullary $bot$"
reading is intrinsic, not an artifact of one presentation.

== Argument 6: conservativity as a proved payoff <sec:conservativity>

Because there is one evaluator and one derivation relation, the relationships
_between_ the rungs are theorems rather than reconstructions.

#theorem([Subsumption chain (`ConservativeChain.lean:152`)])[
  Derivability ascends the tower: `derivability_subsumption_chain` links
  minimal, intuitionistic, and classical derivability of a formula, with the
  per-step maps `derivableMinOfDerivableInt` (`:129`) and
  `derivableIntOfDerivableProp` (`:139`).
]

#theorem([Fragment ladder (`ConservativeChain.lean:226, 246, 270`)])[
  The $bot$-free / connective fragments are conservative over one another:
  `hilbertConjImpConservativeOverImp_direct` (`:226`),
  `hilbertMplConservativeOverImp` (`:246`), and
  `hilbertMplConservativeOverConjImp` (`:270`).
]

On the MPL side, `MplConservativeChain.lean` shows MPL sits at the top of _its
own_ conservativity chain, reached by a direct route rather than by passing
through IPL --- the biconditionals `mplAxiom_iff_conjImpAxiom` (`:197`),
`mplAxiom_iff_conjImpBotMinAxiom` (`:231`), and `mplAxiom_iff_impAxiom` (`:263`),
realizing Benjamin's claim in Zulip #606397657.

Completeness is likewise _one_ theorem with three corollaries, one per rung
(`HilbertCompleteness.lean`):

#theorem([Algebraic completeness (`HilbertCompleteness.lean:64, 93, 122, 155`)])[
  From the single `hilbert_alg_complete_theory` (`:64`) come
  `MPL.hilbert_alg_complete` (`:93`, at `bot_val` free / `GHAValid`),
  `IPL.hilbert_alg_complete` (`:122`, at `bot_val` $= bot$), and
  `CPL.hilbert_alg_complete` (`:155`) as corollaries --- each a biconditional
  between derivability and validity, differing only in the constraint on
  `bot_val`.
]

Finally, the $bot$-free fragment is where the "conservativity by construction"
reading is cleanest: `ghaValid_iff_haValid_of_botFree`
(`FragmentGeneric.lean:174`) shows generalized-Heyting and Heyting validity
_coincide_ on $bot$-free formulas --- informally, the strengthening is faithful
on that fragment. As throughout, "faithful functor" here is an informal reading
of this order-theoretic coincidence, not a formalized `CategoryTheory` claim
(@sec:cat-caveat).
