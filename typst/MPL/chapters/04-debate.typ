// ============================================================================
// 04-debate.typ
// Argument 2: structure-first vs language-first; the Hilbert-vs-ND thread.
// ============================================================================

#import "../template.typ": *
#import "../notation/mpl-notation.typ": *

= The Design Debate <sec:debate>

The design was not settled in a vacuum: it was argued out on the CSLib Zulip,
and the record is worth stating accurately, both because it is the honest
provenance of the design and because the strongest objection to it was never
formally answered. This chapter presents Argument 2 --- structure-first versus
language-first --- and the Hilbert-vs-ND controversy, using the exact message
identifiers so the account is auditable.

#remark("On the status of this chapter")[
  This is an _internal_ report. The messages below are cited by identifier for
  internal traceability. Per the CSLib AI policy --- itself raised in this very
  thread (messages #605827029 / #605840135) --- any prose adapted from this
  chapter for an upstream, community-facing post must be human-authored. This
  document is not such a post.
]

== Argument 2: structure-first vs language-first

The two designs are genuine rivals, and the language-first position has a clear
and reasonable advocate. It should not be caricatured.

*The origin.* Before the redesign (task 407), $bot$ was _not_ a primitive
constructor: it was simulated via a distinguished atom, `[Bot Atom]` --- exactly
the Design-B2 encoding this report argues against. Benjamin flagged this as the
issue to fix (#603163993, 06-15).

*The language-first position (Thomas Waring).* Waring's framing is the cleanest
statement of the alternative (#605341190, 06-21): _"what I've formalised is
minimal natural deduction; the definitions of IPL and CPL should probably be
seen as encodings, rather than a once-and-for-all definition [...] the issue at
hand is whether we want MPL encoded as a fragment of IPL, or IPL encoded in MPL
via the theory construction."_ This is not opposition to a fixed signature
carrying $bot$; it is a considered preference that IPL --- where $bot$ has both
its constructor and its rule --- be treated as the "real" base, with minimal
logic recovered as a fragment or set aside. It is a coherent design philosophy,
and the report represents it as such.

*Independent support for a separate $bot$.* The structure-first side was not
solitary either: Matthew Doty reported agreement with Ching-Tsun Chou _"about a
separate bot constructor"_ (#603877853, 06-16), so a separate-constructor $bot$
had multiple proponents.

*The semantic wrinkle that shaped the evaluator.* Waring also made the
observation that fixed the semantics (#603884159, 06-16): a naive evaluator
sending $bot |-> bot$ unconditionally makes completeness fail for minimal logic.
This is the direct origin of the free `bot_val` parameter of `AlgEvaluate` and
the `bot_forces` field of Kripke forcing (@sec:evaluator) --- the design
_had_ to leave $bot$'s value free at MPL strength to be complete there.

== The decisive substitution post

The argument that turned the structure-first case is Benjamin's
substitution-invariance / free-algebra post (#604219492, 06-17): formulas form
the free algebra over $sig$; substitution is the unique homomorphism extending
an atom map (monadic bind); with primitive $bot$ one gets the unconditional
`| .bot => .bot` case, whereas with $bot$ as an atom, bind sends $bot |->
sigma(bot)$, which can be anything, so one is confined to the subcategory of
$bot$-preserving maps where the universal property fails. This is the message the
module docstring cites by number (`NaturalDeduction/Basic.lean:80-81`), and it
is the source for Argument 1 (@sec:syntax).

== The Hilbert-vs-ND controversy

Conceding the free-algebra point did not end the debate; it relocated it. If
$bot$ is a primitive constructor, should its elimination rule (`efq`) not also be
an unconditional constructor --- restoring the intro/elim symmetry of natural
deduction?

*Benjamin's asymmetry resolution* (#605813681, 06-22): $bot$ is the one
connective with _no introduction rule_ in any standard proof system; the
asymmetry (zero intro rules, one elim rule) is a property of $bot$ itself, not a
defect of the design. This is now baked into the module docstring
(`NaturalDeduction/Basic.lean:92-96`), with citations to Prawitz and to
Troelstra & van Dalen §10.4 and Sørensen & Urzyczyn §2.2.

*Waring's strongest objection, and the open compromise* (#606970606, 06-28 ---
the _last_ message in the thread): _"if we are going to have $bot$ as a
primitive, we should also have efq [...] It seems very unnatural to me to have a
constructor with no semantics, even if that was the original treatment of
Johansson."_ He then proposed a pragmatic compromise: postpone minimal logic to
later work, taking IPL as the base for now. This message received _no recorded
reply_.

#remark("The thread was parked, not ratified")[
  The honest summary is that the Zulip discussion did not _endorse_ Design A ---
  it ended on an unanswered compromise proposal from the design's most
  substantive critic (#606970606). The report states this plainly here and again
  in @sec:honest-limits. The design is defended on its merits (Chapters 1--3),
  not by an appeal to community consensus that was never reached.
]

== Conservativity: contested and resolved with proofs

One strand of the thread did resolve constructively, and it is good evidence
that the framework earns its keep. Waring's request for a semantic
conservativity result was answered by Benjamin's
`ipl_conservative_over_mpl` / `coe_AlgEvaluate` (#605862751, 06-22); Matthew
Doty suggested extending it to a fragment chain (#606026592, 06-23); the
extended chain $"IPL"chevron.l arrow.r, top chevron.r subset dots.h subset "IPL"$
was delivered (#606128428, 06-24); and the MPL-side mirror followed
(#606397657, 06-25). These are the social history behind
`ConservativeChain.lean` and `MplConservativeChain.lean` (@sec:conservativity)
--- the results were contested, requested, and then _proved_, not asserted.
