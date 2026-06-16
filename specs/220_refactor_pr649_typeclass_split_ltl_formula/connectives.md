Thanks for the comments. The latest commit on this branch addresses all
four points:

**1. Future-only temporal operators.**

The commit introduces `FutureTemporalConnectives` (propositional +
until, no since) as a shared base class, and `LTLConnectives` (future +
next) for LTL. The new `LTL.Formula` type has only future-time operators:
`{atom, bot, imp, next, untl}`. The full `TemporalConnectives` (with
`since`) still exists for tense logic (Burgess 1984, Xu 1988), but
`LTL.Formula` does not use it.

**2. Omega-executions of LTS, not just state sequences.**

The current `LTL.Satisfies` uses `v : ℕ → (Atom → Prop)` (a sequence of
valuations). Connection to `LTS.OmegaExecution` — which already carries
both `ss : ωSequence State` and `μs : ωSequence Label` — is noted as
future work in the module doc. A follow-up PR can define satisfaction
directly over `OmegaExecution` pairs.

**3. Talking about LTS transitions.**

Related to point 2. `LTS.OmegaExecution` already carries transition
labels `μs`. A natural next step is to parameterise LTL atoms over both
state predicates and transition labels, so formulas can refer to
transitions as well as states.

**4. Encodable/Countable/Infinite/Denumerable.**

Agreed — removed. The latest commit strips all
Encodable/Countable/Infinite/Denumerable instances and BEq
reflexivity/lawfulness proofs from `Temporal.Formula`, deferring them
to a future completeness PR where they are actually needed.

**5. Büchi automata and ω-regular languages.**

The `LTL.Satisfies` semantics over ω-words (`v : ℕ → (Atom → Prop)`) are
designed with compatibility in mind for the existing Büchi automata and
ω-regular language infrastructure in `Cslib.Computability`. A natural
follow-up is to prove the LTL-to-Büchi translation theorem, connecting
`LTL.Satisfies` to `ωLanguage.IsRegular` via the existing boolean closure
results (union, intersection, complementation).
