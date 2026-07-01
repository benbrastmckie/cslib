// ============================================================================
// 01-syntax.typ
// Argument 1: the free monad on the signature; substitution invariance.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= Syntax and the Free Monad <sec:syntax>

The starting point of the whole design is a single choice: the type of formulas
is the free algebra --- equivalently, the free monad --- on the fixed signature
$sig$. This chapter presents that type, the substitution operation it carries,
and the argument (Argument 1) that this choice is what makes $bot$ behave like a
primitive rather than a placeholder.

== The `Proposition` type

#definition("Formulas")[
  For a type $"Atom"$ of atomic propositions, the type `Proposition Atom` is
  defined inductively with five primitive constructors:
  $ phi.alt, psi ::= p | bot | phi.alt arrow.r psi | phi.alt and psi | phi.alt or psi $
  where $p$ ranges over atoms. The constructor $bot$ is _nullary_: it takes no
  arguments (`Defs.lean:81-92`, with `bot` at line 85).
]

The essential structural fact is visible already in the constructor list:
$bot$ sits alongside the binary connectives as an operation of the signature,
_not_ alongside $p$ as a generator. An atom is a hole that substitution may
fill; $bot$ is not.

#figure(
  table(
    columns: 4,
    stroke: none,
    align: left,
    table.hline(),
    table.header(
      [*Symbol*], [*Name*], [*Lean*], [*Reading*],
    ),
    table.hline(),
    [$p, q, r$], [Atom], [`atom x`], [sentence letter],
    [$bot$], [Bottom], [`bot`], [falsity (nullary operation)],
    [$phi.alt arrow.r psi$], [Implication], [`imp`], ["if $phi.alt$ then $psi$"],
    [$phi.alt and psi$], [Conjunction], [`and`], ["$phi.alt$ and $psi$"],
    [$phi.alt or psi$], [Disjunction], [`or`], ["$phi.alt$ or $psi$"],
    table.hline(),
  ),
  caption: [The five primitive constructors of `Proposition` (`Defs.lean:81-92`).],
)

Negation, truth, and the biconditional are _derived_, not primitive
(`Defs.lean:95-102`):

#definition("Derived operators")[
  $
    not phi.alt &:= phi.alt arrow.r bot \
    top &:= bot arrow.r bot \
    phi.alt arrow.l.r psi &:= (phi.alt arrow.r psi) and (psi arrow.r phi.alt)
  $
]

Note that $top := bot arrow.r bot$ imposes nothing on $bot$ at MPL strength: it
is a theorem of the pure implicational fragment and holds whatever $bot$ turns
out to mean. This is the first sign that, at the base, $bot$ is genuinely
unconstrained.

== Substitution and the monad

Substitution renames atoms, possibly changing the atomic language, and is
defined by the obvious structural recursion (`Defs.lean:128-134`):

#definition("Substitution")[
  For $f : "Atom" arrow.r "Proposition Atom'"$, the map
  `subst` $f : "Proposition Atom" arrow.r "Proposition Atom'"$ is:
  $
    "subst" f (p) &= f(p) \
    "subst" f (bot) &= bot \
    "subst" f (phi.alt arrow.r psi) &= "subst" f (phi.alt) arrow.r "subst" f (psi) \
    "subst" f (phi.alt and psi) &= "subst" f (phi.alt) and "subst" f (psi) \
    "subst" f (phi.alt or psi) &= "subst" f (phi.alt) or "subst" f (psi)
  $
]

The decisive line is the second: `| bot => .bot` (`Defs.lean:131`). It is
_unconditional_. There is no side condition $sigma(bot) = bot$ to discharge, no
decidability branch distinguishing $bot$ from an atom --- $bot$ is fixed by
_every_ substitution because it is an operation of the signature and
substitution is a signature homomorphism. This one-line case is the concrete
content of "substitution invariance".

The type then carries a monad structure in which return is `atom` and bind is
substitution (`Defs.lean:137-139`):

#definition("The substitution monad")[
  $
    "pure" &:= "atom" quad quad "bind" A f := "subst" f (A)
  $
  so that `Proposition` is a monad with $"pure" = eta$ (the insertion of
  generators) and bind given by substitution.
]

#remark("Free monad --- an informal reading")[
  Externally, `Proposition Atom` is the free monad on the signature functor
  $Sigma X = bb(1) + X^2 + X^2 + X^2$ (the nullary $bot$ in the $bb(1)$ summand,
  the three binary connectives in the $X^2$ summands) over the generators
  $"Atom"$; substitution is the unique extension of $f$ to a monad morphism, and
  the nullary-operation homomorphism law _forces_ $"subst" f (bot) = bot$.

  This is a description of what the code realizes, and it is deliberately
  labelled as such. The source itself is careful here: the comment immediately
  above the `Monad` instance reads _"This is probably a lawful monad, but that
  doesn't seem to be important"_ (`Defs.lean:136`), and _no_ `LawfulMonad
  Proposition` instance is declared. There is likewise no
  `CategoryTheory.Adjunction` or `Functor` instance anywhere in the
  propositional development (@sec:cat-caveat). The free-monad framing is a
  faithful external account of the inductive-plus-`subst` pair; it is not a
  Lean-proved universal property.
]

== Argument 1: why the signature choice matters

The reason the signature choice is not a mere convention is that it fixes the
_ontology_ of $bot$ under substitution. The design docstring states the point
directly (`NaturalDeduction/Basic.lean:66-100`):

#remark([The docstring's statement (`NaturalDeduction/Basic.lean:66-100`)])[
  _"The canonical justification for Design A is substitution-invariance: any
  renaming of atoms that sends $p_0 |-> bot$ must commute with derivability. If
  $bot$ were treated as a meta-symbol excluded from the language, the language
  would fail to be closed under propositional substitution [...] This is also
  the free-algebra argument: the type `Proposition Atom` is the free monad on
  ${bot, arrow.r, and, or}$, so $bot$ is an element of this algebra, not an
  external constant."_
]

This is realized, not merely asserted, at the level of derivations. The
operation `substAtom` transports a derivation along a substitution
(`NaturalDeduction/Basic.lean:392-408`), and its explosion case
(`efq`, line 408) re-derives explosion _in the substituted theory_ via
`IsIntuitionistic.efq` on the new theory --- with no hypothesis $sigma(bot) =
bot$ anywhere in its type. Substitution of derivations is therefore total and
side-condition-free, exactly because $bot$ is a signature operation.

#remark("What Argument 1 does and does not establish")[
  Argument 1 establishes that _given_ a single formula type shared across
  MPL / IPL / CPL (and, downstream, the modal and temporal logics), treating
  $bot$ as a nullary operation is what removes the $sigma(bot) = bot$ side
  condition and keeps one substitution monad for all of them. It does _not_ by
  itself single out the signature: declaring $bot$ a _generator_ also yields a
  free monad. The universal-property phrasing restates the choice rather than
  forcing it. The argument that the operation-choice carries a genuine _further_
  payoff --- that it makes the tower of logics a chain of varieties --- is the
  keystone, and it is developed in @sec:semantics. The deciding Zulip message
  for the substitution framing is #604219492.
]
