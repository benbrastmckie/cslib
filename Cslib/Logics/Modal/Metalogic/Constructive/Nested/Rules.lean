/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Context

/-! # The `NCK` Nested-Sequent Proof System

This module encodes Arisaka–Das–Straßburger's base cut-free proof system `NCK` for `CK`
(`doc_id: arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics`, §3, Figure 2),
as an inductive proof-tree family `NestedProof` indexed by conclusion, following `Nested/Context
.lean`'s `InputCtx`/`OutputCtx` hole-filling apparatus (Observation 2.2, Definition 2.3). Verified
against the recovered source PDF (cross-checked via both direct page rendering and
`pdftotext -f 6 -l 7 -layout`, since `pdftotext` silently drops the `□` glyph in this PDF's font
encoding -- confirmed again this phase).

## Which Context Kind Each Rule Uses

Figure 2's rules display a `Γ{ }` schema whose hole is filled with either LHS-typed content
(`A•`), RHS-typed content (`A°`), or a full-sequent pair. Phase 7's `Nested/Context.lean` built
exactly four hole-filling operations (Observation 2.2), and which one a given rule needs is
forced by the *type* of what fills the hole, not a free stylistic choice:

* **LHS-typed hole content** (`id`, `⊥•`, `∧•`, `∨•`, `⊃•`'s second premise and conclusion, `□•`,
  `♦•`, `c`): `OutputCtx.fillLhs` alone only yields a bare `NestedLhs`, not a full sequent, so
  these rules need the extra output-formula companion `Definition 2.3`'s `InputCtx` supplies.
  Every one of these rules therefore takes `ctx : InputCtx Atom` and is stated via `ctx.fillLhs`,
  with `ctx.π` playing the role of the rule's (possibly implicit, possibly explicit) companion
  `Π°`. This also explains, for free, why `⊥•` and `∨•`'s side condition ("the output formula
  must be in the same subtree as the principal formula", noted in the source directly after
  Figure 2) needs no separate Lean-level hypothesis: `InputCtx.fillLhs`'s definition (`ctx.Γ'
  .fillRhs (.box (ctx.Λ.fillLhs Δ) ctx.π)`) *always* places the hole and `ctx.π` as the two direct
  children of one shared `box`, i.e. the same subtree, by construction.
* **RHS-typed hole content** (`∧°`, `∨°` (both injections), `⊃°`'s premise, `□°`): `OutputCtx
  .fillRhs`/`.fillFull` already close a bare output context directly into a full sequent, with no
  extra companion needed. These rules take `ctx : OutputCtx Atom`.
* **`⊃•`'s first premise and `◇°`'s conclusion** need `OutputCtx.fillFull`/the output-pruning
  operation specifically, not `fillRhs` alone: `⊃•`'s first premise is `Γ⇓{A°}` (`ctx.outputPruning
  .fillRhs`, Definition 2.3 -- "the output pruning is defined differently from [Str13]: there
  only the unique output formula is removed, whereas here the whole subtree containing the output
  formula is removed", matching Phase 7's `Γ' ++ Λ`); `◇°`'s conclusion `Γ{◇A°,[Δ]}` mixes an
  RHS leaf (`◇A°`) with an LHS bracket (`[Δ]`) at the same level, which cannot be a single
  `NestedRhs` filler (`NestedRhs` has no comma constructor), so it is `ctx.fillFull (.dia Δ, ...)`
  -- a genuine full-sequent pair, not a bare RHS sequent.

## The Contraction Rule `c`

The source explicitly notes (§3, directly after Figure 2's introduction) that unlike
Straßburger's intuitionistic system ([Str13]) and Brünnler's classical one ([Brü09]), which use
*additive* versions of `⊃•`/`□•` and can leave contraction admissible, this system must make
contraction an explicit primitive rule: "here it is necessary to make contraction explicit since
our treatment of the b-axiom does not allow us to show the admissibility of contraction... our
cut-elimination proof differs significantly from the ones in [Str13] and [Brü09]." `c` is landed
here as a primitive `NestedProof` constructor, not derived.

## Smoke-Test Derivations, Not a Literal §3 Transcription

The source's own §3 text, between Figure 2 and Proposition 3.1 ("the general `id`-rule ... is
derivable [by] a straightforward induction"), does not display any concrete derivation trees to
transcribe verbatim (confirmed by a full-document grep for "Example", which surfaces only
Example 2.1 -- already landed in Phase 6/7 -- and much later, unrelated examples in §6). Proposition
3.1 itself is a genuine standalone induction over formula structure (deferred to a later phase,
not landed here as a "smoke test"): its base case needs the *atomic* `id` axiom to be reachable
from a bare top-level goal `Γ{A•,A°}` at `ctx = []`, but `InputCtx.fillLhs` structurally forces
one `box` between the hole and `ctx.π` no matter how short `ctx.Γ'`/`ctx.Λ` are (see the
docstring note above), so a flat, box-free `(A•, A°)` premise is not directly reachable from `id`
at all -- exactly the sort of induction-over-`A` argument Proposition 3.1 promises, not a smoke
test. This section instead lands small, honestly-labelled illustrative examples confirming
`NestedProof` compiles and its rules combine end-to-end: bare instances of the two axioms, and one
genuine multi-rule combination (`∨•` applied to two `⊥•` instances).

## `NCS5`: the Safe-Pair Extension `NCK′ + {t,4}#_G + {b}[]`

The source parameterises its rule families by two axiom sets `X, Y ⊆ {d,t,b,4,5}` (§3, directly
below Figure 4): `X^◘` denotes the Figure 3 (`□•`/`◇°`-style) rules for members of `X`, and `Y^[]`
denotes the Figure 4 *structural* rules for members of `Y`; `NCK + X^◘ + Y^[]` is then `NCK`

**Theorem 5.2's exact side conditions, verified against page 14** (`Theorem 5.2 (Cut-free
Completeness)`): "Let `X ⊆ {d,t,4}` and `Y ⊆ {d,b,5}`, such that if `t ∈ X` and `5 ∈ Y` then
`b ∈ Y`, and if `b ∈ Y` then `4 ∈ X`. Then every formula that is provable in `HCK+X+Y` is also
provable in `NCK′+X^◘+Y^[]`." For `CS5`'s `X = {t,4}`, `Y = {b}`: the first conditional
(`t ∈ X ∧ 5 ∈ Y → b ∈ Y`) is vacuously true since `5 ∉ Y`; the second (`b ∈ Y → 4 ∈ X`) holds
since both `b ∈ Y` and `4 ∈ X`. Theorem 5.2 explicitly lists `CS5` among the cube logics this
covers ("Theorem 5.2 gives us cut-free systems for the logics `CK, CK4, CK45, CD, CD4, CD45, CT,
CS4,` and `CS5`"). This matches the base type restriction too: `X ⊆ {d,t,4}` and `Y ⊆ {d,b,5}`
are *disjoint* domains in Theorem 5.2 itself (`t`/`4` only ever appear in `X`, `b`/`5` only ever
in `Y`), confirming that `{t,4}` belongs to Figure 3's `X^◘` rules and `{b}` to Figure 4's `Y^[]`
rules, not the reverse or a mix.
augmented with both. `CS5`'s safe pair is `X = {t,4}`, `Y = {b}` (Theorem 5.2 names `CS5`
explicitly in its covered-logic list) -- so `NCS5` needs exactly `t°`, `t•`, `4°`, `4•` (Figure 3,
page 7, since `t,4 ∈ X`) and the structural `b^[]` (Figure 4, page 8, since `b ∈ Y`); `d^[]`,
`t^[]`, `4^[]`, `5^[]` and the naive `b°_int`/`b°_con`/`b•_int`/`b•_con` (eq. (3.2)/(3.3), shown
sound-but-incomplete on page 8) are all out of scope for this instance. Landed as five additional
`NestedProof` constructors on the *same* inductive (not a new indexed type), so a later cube
generalisation over other `X, Y` only adds constructors, never rewrites existing ones.

Verified against direct renders of PDF pages 7 (Figure 3) and 8 (Figure 4); `pdftotext` was cross-
checked and, consistent with Phase 9's finding, silently drops or garbles the `□`/`◇` glyphs at
several of these rules' positions, so the direct page render is the authoritative source used
below, not the `pdftotext` extraction.

* **`t°`** (`Γ{A°} / Γ{◇A°}`) and **`t•`** (`Γ{A•} / Γ{□A•}`): no bracket at all on either side, so
  both are direct `fillRhs`/`fillLhs` applications with no `.box`/`.dia` wrapper -- `t°` is
  `OutputCtx.fillRhs` (RHS-typed content, same shape as `andR`/`boxR`), `t•` is
  `InputCtx.fillLhs` (LHS-typed content, needs the `π` companion, same shape as `boxL`/`diaL`).
* **`4°`** (`Γ{[◇A°,Δ]} / Γ{◇A°,[Δ]}`) and **`4•`** (`Γ{[□A•,Δ]} / Γ{□A•,[Δ]}`): structurally
  identical in shape to `diaR`/`boxL` (Figure 2) respectively -- same premise/conclusion context
  pattern (`OutputCtx.fillRhs (.box Δ ·)` / `ctx.fillFull (.dia Δ, ·)` for `4°`;
  `InputCtx.fillLhs (.dia (.comma · Δ))` / `InputCtx.fillLhs (.comma · (.dia Δ))` for `4•`) -- but
  with the leaf fixed at the *already-formed* `◇A°`/`□A•` on both sides, rather than being built
  up from a bare `A°`/`A•` as `diaR`/`boxL` do. This is a genuinely different rule from `NCK`'s
  own `◇°`/`□•` (confirmed by comparing Figure 2's `◇°`/`□•` premises, which build the modal
  formula fresh from a bare leaf, against Figure 3's `4°`/`4•` premises, which reposition an
  already-modalised formula), not a duplicate.
* **`b^[]`** (`Γ{[[Σ],Δ]} / Γ{Σ,[Δ]}`): a genuinely *structural* rule -- `Σ`, `Δ` carry no
  polarity superscript in the source (its own convention: unmarked capital Greek denotes an
  arbitrary sequent), unlike Figure 2/3's rules which build up one polarity-tagged formula at a
  time. Since `,` and `[·]` at this position are both `NestedLhs`-level constructors
  (`NestedLhs.comma`/`NestedLhs.dia`; only `NestedRhs.box` could give a different reading, but that
  constructor's own bracket notation is the two-argument `[Φ,Ψ]` form, not this single-argument
  `[Σ]`/`[[Σ],Δ]` shape), both `Σ` and `Δ` are typed `NestedLhs Atom`, and the whole rule needs
  `InputCtx.fillLhs` (LHS-typed content, same necessity argument as `contract`/`boxL`/`diaL`).
  This is the source's own replacement for the incomplete eq. (3.2)/(3.3) `b°`/`b•` rules (page 8:
  "To address this problem, we introduce the structural rules in Figure 4 ... The first ... is
  sound in the constructive setting").

## `NestedProof.mono`: Index-Transport Precursor to Phase 19's Weakening

The plan's Phase 10 task list asks to "land weakening/`.mono` transport," mirroring the
`SeqProof.mono`/`LJProof.mono`/`CutFreeLJProof.mono` weakening-transport family in
`Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean`. This module lands `NestedProof.mono`
as the **index-equality transport** (`Γ = Γ' → NestedProof Γ → NestedProof Γ'`), height-preserving
(hence height-non-increasing, matching this phase's own verification criterion literally) --
**not yet** the genuine content-weakening admissible rule (Figure `(3.1)`'s `w`: `Γ{∅} / Γ{Δ•}`
for arbitrary `Δ`, which the source itself states is proved admissible only much later, alongside
`nec`/`cut`). The plan's own Phase 19 ("Height-preserving admissibility of the structural rules")
explicitly names its first task "extend Phase 10's `.mono` to the height-preserving statement" --
confirming this phase's `.mono` is deliberately the narrower precursor, not a premature (and
unbudgeted, within this phase's 2.5-hour scope) attempt at the full admissibility induction over
all eighteen constructors, which is Phase 19's dedicated `Admissibility.lean`. Separately, and for
free: since `NCS5` is realised as five *additional* constructors on the same `NestedProof`
inductive rather than a new type, every `NCK′` (Phase 9) proof is automatically an `NCS5` proof
of unchanged height with no transport lemma needed for that inclusion direction.

## References

* [R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*][ArisakaDasStrassburger2015], §3, Figure 2 (system `NCK`), Figure 3 (page 7, `d`/`t`/`4`
  logical rules), Figure 4 (page 8, structural rules for `d`/`t`/`b`/`4`/`5`), the `X^◘`/`Y^[]`
  parameterisation directly below Figure 4, and Theorem 5.2 (page 14, cut-free completeness side
  conditions, confirming the `CS5` safe pair `X = {t,4}`, `Y = {b}`).
-/

@[expose] public section

namespace Cslib.Logic.Modal

universe u
variable {Atom : Type u}

/-! ## The `NCK` Proof System (Figure 2) -/

/-- The `NCK` nested-sequent proof system: an inductive family of proof trees indexed by their
conclusion. Following the source's own convention ("A proof of a formula `A` is ... a derivation
whose conclusion is the (full) sequent `A°`"), a `NestedProof` term with conclusion
`(NestedLhs.empty, NestedRhs.atom A)` is a proof of the formula `A`. Each constructor is named
after its Figure 2 rule label; see the module docstring for why each one takes an `InputCtx` or
an `OutputCtx`. -/
inductive NestedProof : NestedFull Atom → Type u where
  /-- `⊥•`: `Γ{⊥•,Π°}` is an axiom, for every input context `ctx`. -/
  | botL (ctx : InputCtx Atom) : NestedProof (ctx.fillLhs (.atom .bot))
  /-- `id`: `Γ{a•,a°}` is an axiom, for every atomic `a : Atom` and every choice of the
  surrounding output-context shells `Γ'`, `Λ` (the input context's `π` component is forced to be
  `a°` itself, matching the rule's own `a` appearing on both sides). -/
  | id (Γ' Λ : OutputCtx Atom) (a : Atom) :
      NestedProof ((⟨Γ', Λ, .atom (.atom a)⟩ : InputCtx Atom).fillLhs (.atom (.atom a)))
  /-- `∧•`: from the comma of both input conjuncts, derive their conjunction. -/
  | andL (ctx : InputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillLhs (.comma (.atom A) (.atom B))) →
      NestedProof (ctx.fillLhs (.atom (A.and B)))
  /-- `∧°`: from separate proofs of both output conjuncts, derive their conjunction. -/
  | andR (ctx : OutputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillRhs (.atom A)) → NestedProof (ctx.fillRhs (.atom B)) →
      NestedProof (ctx.fillRhs (.atom (A.and B)))
  /-- `∨•`: case-split input disjunction, the shared companion `Π°` is `ctx.π`. -/
  | orL (ctx : InputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillLhs (.atom A)) → NestedProof (ctx.fillLhs (.atom B)) →
      NestedProof (ctx.fillLhs (.atom (A.or B)))
  /-- `∨°` (left injection): from a proof of `A°`, derive `(A ∨ B)°`. -/
  | orRLeft (ctx : OutputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillRhs (.atom A)) → NestedProof (ctx.fillRhs (.atom (A.or B)))
  /-- `∨°` (right injection): from a proof of `B°`, derive `(A ∨ B)°`. -/
  | orRRight (ctx : OutputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillRhs (.atom B)) → NestedProof (ctx.fillRhs (.atom (A.or B)))
  /-- `⊃•`: input implication. The first premise uses the *output pruning* `ctx.outputPruning`
  (Definition 2.3), not `ctx` itself -- matching the source's remark that this rule (and later
  `cut`) prune the whole subtree containing the output formula. -/
  | impL (ctx : InputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.outputPruning.fillRhs (.atom A)) → NestedProof (ctx.fillLhs (.atom B)) →
      NestedProof (ctx.fillLhs (.atom (A.imp B)))
  /-- `⊃°`: output implication, from a proof of the full sequent `(A•, B°)` filling `ctx` via
  `OutputCtx.fillFull` -- the premise carries both polarities at once, so it cannot be a bare
  `fillRhs` filler. -/
  | impR (ctx : OutputCtx Atom) (A B : Proposition Atom) :
      NestedProof (ctx.fillFull (.atom A, .atom B)) →
      NestedProof (ctx.fillRhs (.atom (A.imp B)))
  /-- `□•`: pulls `A•` out of a `◇`-bracket shared with auxiliary content `Δ`, replacing it with
  the formula `□A•` and leaving `[Δ]` behind. -/
  | boxL (ctx : InputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom) :
      NestedProof (ctx.fillLhs (.dia (.comma (.atom A) Δ))) →
      NestedProof (ctx.fillLhs (.comma (.atom (Proposition.box A)) (.dia Δ)))
  /-- `□°`: collapses the trivial (empty-LHS) box bracket `[A°]` into the formula `□A°`. -/
  | boxR (ctx : OutputCtx Atom) (A : Proposition Atom) :
      NestedProof (ctx.fillRhs (.box .empty (.atom A))) →
      NestedProof (ctx.fillRhs (.atom (Proposition.box A)))
  /-- `♦•`: collapses the trivial `◇`-bracket `[A•]` into the formula `♦A•`. -/
  | diaL (ctx : InputCtx Atom) (A : Proposition Atom) :
      NestedProof (ctx.fillLhs (.dia (.atom A))) →
      NestedProof (ctx.fillLhs (.atom (Proposition.diamond A)))
  /-- `◇°`: dual of `□•` on the output side. The premise fills `ctx`'s hole with the RHS box
  bracket `[Δ, A°]`; the conclusion fills the *same* `ctx`'s hole with the full-sequent pair
  `(◇A°, [Δ])` via `OutputCtx.fillFull` (see the module docstring for why `fillRhs` alone cannot
  express this conclusion). -/
  | diaR (ctx : OutputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom) :
      NestedProof (ctx.fillRhs (.box Δ (.atom A))) →
      NestedProof (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A)))
  /-- `c`: explicit contraction, contracting two comma-adjacent copies of the same LHS sequent
  `Δ` into one. Necessary as a primitive here (not admissible), per the source's own remark --
  see the module docstring. -/
  | contract (ctx : InputCtx Atom) (Δ : NestedLhs Atom) :
      NestedProof (ctx.fillLhs (.comma Δ Δ)) → NestedProof (ctx.fillLhs Δ)
  /-- `t°`: `Γ{A°}` derives `Γ{◇A°}` -- no bracket, direct `fillRhs` on both sides. See the module
  docstring's "`NCS5`: the Safe-Pair Extension" section for why exactly these five constructors
  (not the full `X, Y ⊆ {d,t,b,4,5}` cube) realise `CS5`'s safe pair `X = {t,4}`, `Y = {b}`. -/
  | tR (ctx : OutputCtx Atom) (A : Proposition Atom) :
      NestedProof (ctx.fillRhs (.atom A)) →
      NestedProof (ctx.fillRhs (.atom (Proposition.diamond A)))
  /-- `t•`: `Γ{A•}` derives `Γ{□A•}` -- no bracket, direct `fillLhs` on both sides. -/
  | tL (ctx : InputCtx Atom) (A : Proposition Atom) :
      NestedProof (ctx.fillLhs (.atom A)) →
      NestedProof (ctx.fillLhs (.atom (Proposition.box A)))
  /-- `4°`: repositions an already-formed `◇A°` out of a box shared with auxiliary `Δ`, same
  context shape as `◇°` (`diaR`) but with the leaf fixed at `◇A°` rather than built from bare
  `A`. -/
  | fourR (ctx : OutputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom) :
      NestedProof (ctx.fillRhs (.box Δ (.atom (Proposition.diamond A)))) →
      NestedProof (ctx.fillFull (.dia Δ, .atom (Proposition.diamond A)))
  /-- `4•`: repositions an already-formed `□A•` out of a `◇`-bracket shared with auxiliary `Δ`,
  same context shape as `□•` (`boxL`) but with the leaf fixed at `□A•` rather than built from bare
  `A`. -/
  | fourL (ctx : InputCtx Atom) (A : Proposition Atom) (Δ : NestedLhs Atom) :
      NestedProof (ctx.fillLhs (.dia (.comma (.atom (Proposition.box A)) Δ))) →
      NestedProof (ctx.fillLhs (.comma (.atom (Proposition.box A)) (.dia Δ)))
  /-- `b^[]`: the Figure 4 structural rule for the `b`-axiom, replacing the incomplete eq.
  (3.2)/(3.3) `b°`/`b•` rules. `σ` (source's `Σ`), `Δ` are generic `NestedLhs` sequents (no
  polarity marker in the source), not single formulas. (Spelled lowercase `σ`, not capital `Σ`:
  Mathlib binds capital `Σ` as sigma-type binder notation, unusable as a plain identifier here --
  the same clash `Nested/Context.lean`'s docstring already documents for capital `Π` vs. `π`.) -/
  | bStruct (ctx : InputCtx Atom) (σ Δ : NestedLhs Atom) :
      NestedProof (ctx.fillLhs (.dia (.comma (.dia σ) Δ))) →
      NestedProof (ctx.fillLhs (.comma σ (.dia Δ)))

/-! ## Proof Height -/

/-- Proof height: `0` for the two axioms (`⊥•`, `id`), and `1 +` the max premise height for every
rule with one or two premises. Structural recursion on the `NestedProof` term itself; the
conclusion index is universally quantified (`∀ {Γ}, ...`, not fixed via `variable`) since every
recursive call is at a different `NestedFull Atom` index than the outer conclusion. -/
def NestedProof.height : ∀ {Γ : NestedFull Atom}, NestedProof Γ → Nat
  | _, .botL _ => 0
  | _, .id .. => 0
  | _, .andL _ _ _ p => p.height + 1
  | _, .andR _ _ _ p q => max p.height q.height + 1
  | _, .orL _ _ _ p q => max p.height q.height + 1
  | _, .orRLeft _ _ _ p => p.height + 1
  | _, .orRRight _ _ _ p => p.height + 1
  | _, .impL _ _ _ p q => max p.height q.height + 1
  | _, .impR _ _ _ p => p.height + 1
  | _, .boxL _ _ _ p => p.height + 1
  | _, .boxR _ _ p => p.height + 1
  | _, .diaL _ _ p => p.height + 1
  | _, .diaR _ _ _ p => p.height + 1
  | _, .contract _ _ p => p.height + 1
  | _, .tR _ _ p => p.height + 1
  | _, .tL _ _ p => p.height + 1
  | _, .fourR _ _ _ p => p.height + 1
  | _, .fourL _ _ _ p => p.height + 1
  | _, .bStruct _ _ _ p => p.height + 1

/-! ## `NestedProof.mono`: Index-Transport Precursor to Phase 19's Weakening

See the module docstring's "`NestedProof.mono`" section for why this is the index-equality
transport precursor to the later content-weakening admissibility theorem, not that theorem
itself. -/

/-- Transport a `NestedProof` along a propositional equality of its `NestedFull` index. Mirrors
the `SeqProof.mono`/`LJProof.mono` weakening-transport family in
`Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean`, restricted (for this phase) to the
index-equality case. -/
def NestedProof.mono {Γ Γ' : NestedFull Atom} (h : Γ = Γ') (d : NestedProof Γ) : NestedProof Γ' :=
  h ▸ d

/-- `NestedProof.mono` does not increase height: it is in fact height-*preserving*, since it is a
pure index transport rather than an insertion of new rule steps. Matches this phase's own
verification criterion ("`.mono` is height-non-increasing"). -/
theorem NestedProof.mono_height {Γ Γ' : NestedFull Atom} (h : Γ = Γ') (d : NestedProof Γ) :
    (d.mono h).height ≤ d.height := by
  subst h
  exact Nat.le_refl _

/-! ## Smoke-Test Derivations

See the module docstring's "Smoke-Test Derivations, Not a Literal §3 Transcription" section for
why these are illustrative examples rather than a source transcription. -/

/-- `⊥•` axiom instance: `Γ{⊥•,Π°}` typechecks directly as an axiom application, for any input
context `ctx`, with no premises. -/
example (ctx : InputCtx Atom) : NestedProof (ctx.fillLhs (.atom .bot)) := .botL ctx

/-- `id` axiom instance for a fixed atom `a`, at the trivial (`Γ' = Λ = []`) surrounding context:
`Γ{a•,a°}` typechecks directly as an axiom application. -/
example (a : Atom) :
    NestedProof ((⟨[], [], .atom (.atom a)⟩ : InputCtx Atom).fillLhs (.atom (.atom a))) :=
  .id [] [] a

/-- A genuine multi-rule derivation (not a bare axiom): `∨•` applied to two `⊥•` instances derives
`Γ{(⊥ ∨ ⊥)•,Π°}`, for any input context `ctx`, confirming the propositional rules combine with
the axioms as expected. -/
example (ctx : InputCtx Atom) :
    NestedProof (ctx.fillLhs (.atom (Proposition.bot.or Proposition.bot))) :=
  .orL ctx .bot .bot (.botL ctx) (.botL ctx)

end Cslib.Logic.Modal
