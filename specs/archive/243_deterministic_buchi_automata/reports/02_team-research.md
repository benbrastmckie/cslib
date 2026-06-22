# Research Report: Task 243 — DBA Constructions (Team Synthesis)

**Task**: Deterministic Büchi automata constructions and related results
**Date**: 2026-06-20
**Mode**: Team Research (4 teammates, standard mode)
**Completed**: 2026-06-20

---

## Executive Summary

The team's combined investigation confirms that CSLib's DA/ directory provides a strong
foundation for adding DBA closure and characterization results, but several concrete
prerequisites are missing and one source claim must be corrected. Three uniform findings
emerged across all four teammates: (1) `DA.prod_run_eq` — the ω-level decomposition of
the product run — does not exist in CSLib and is the single hard blocker for both union
and intersection proofs; (2) Mathlib contains no omega-automata infrastructure, making
CSLib's stack the sole reference point; and (3) the DBA union proof is clean once the
prerequisite lemma is in place, while the Landweber theorem requires substantially more
effort than the prior survey estimated.

The most significant conflict between teammates concerns the Landweber forward-direction
proof: Teammate A and the prior survey characterize Thomas 2003 Ch. 3 as providing a
"complete proof in both directions," but Teammate C's adversarial review establishes that
the forward direction contains an undefined term ("outnumbered") and that the reset
condition must be independently derived. The revised estimate for Landweber alone is
500-700 lines rather than 300-400. A secondary correction: the DBA complement non-closure
proof is not "essentially free" — it requires constructing a concrete 2-state DBA
for "infinitely many 1s" (~30-40 lines), though the non-recognizability witness is already
in CSLib.

Strategically (Teammate D), task 243 fills a missing architectural stratum between raw type
definitions and language-level results. The recommended output is two stacked PRs: closure
properties first (union, intersection, complement non-closure), then Landweber plus the
DBA → DMA conversion. The DBA → DMA conversion belongs in task 243, not task 252, because
it is needed by task 241 (McNaughton) and logically belongs with the DBA characterization.

---

## Key Findings

### 1. DA Infrastructure Is Correct but Stratified (All teammates, High confidence)

The DA directory (`Cslib/Computability/Automata/DA/`) uses a clean type hierarchy:
`DA.Buchi` and `DA.Muller` both extend `DA` (not each other), sharing a single `toDA`
field. The product construction `DA.prod` exists in `DA/Prod.lean` with `prod_mtr_eq`
(finite-word decomposition). All four teammates confirmed this layout from direct
inspection.

The existing file sizes provide calibration for estimates:
- `BuchiInter.lean`: 137 lines (not ~350 as the prior survey assumed — Teammate C corrected
  this from direct measurement)
- `BuchiCompl.lean`: ~275 lines, but with `proof_wanted` for the hard direction
- `BuchiCongruence.lean`: ~234 lines

### 2. `DA.prod_run_eq` Is the Critical Missing Prerequisite (All teammates, High confidence)

The finite-word analog `DA.prod_mtr_eq` exists, but its ω-level counterpart does not:

```lean
-- NEEDED — not currently in CSLib
@[simp]
theorem DA.prod_run_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    (da1.prod da2).run xs n = (da1.run xs n, da2.run xs n)
```

Proof: straightforward induction on `n` using `run_zero`, `run_succ`, and `FLTS.prod.tr`.
Estimated effort: ~10 lines. Target file: `DA/Prod.lean`. This lemma is required by both
the union and intersection correctness proofs, and must be Phase 1, Step 0.

### 3. DBA Union Is Straightforward via `Filter.frequently_or_distrib` (Teammates A, B, C; High confidence)

The union construction places the product DA with `accept = (F₁ ×ˢ Set.univ) ∪ (Set.univ ×ˢ F₂)`.
The correctness proof does not require a separate pigeonhole argument: `Filter.frequently_or_distrib`
(in `Mathlib.Order.Filter.Basic`, already used in `BuchiInter.lean` line 111) directly gives:

```
(∃ᶠ k, p k ∨ q k) ↔ (∃ᶠ k, p k) ∨ ∃ᶠ k, q k
```

Teammate B had noted some uncertainty about whether this sufficed or whether `frequently_in_finite_type`
was needed; Teammate C confirmed `frequently_or_distrib` is sufficient and more direct. The only
obstacle is `DA.prod_run_eq`.

### 4. DBA Intersection Requires New Deterministic Counter Construction (Teammates A, B, C; High confidence)

The NBA intersection in `NA/BuchiInter.lean` uses `NA.addHist` built on nondeterministic
`LTS` (relational transitions). There is no `DA.addHist` analog. The DBA intersection
must be written fresh, with the counter transition inlined. The 3-state counter (`Fin 3`)
following Thomas 2003 Ch. 1 is the correct approach and is accepted by all teammates:

```lean
noncomputable def DA.Buchi.inter (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2 × Fin 3) Symbol
```

The `noncomputable` annotation is required because the counter transition checks `s ∈ a.accept`,
which requires `Classical.em`. This is consistent with CSLib's existing approach in `BuchiInter.lean`.

### 5. DBA Complement Non-Closure Requires a Concrete 2-State DBA (Teammates B, C; High confidence)

The prior survey characterized this proof as "essentially free," but Teammate C established
that constructing a concrete 2-state DBA for "infinitely many 1s" is still required (~30-40
lines). The non-recognizability of the complement (`eventuallyZero`) is already proved via
`IsRegular.not_da_buchi`. The proof structure is:
- Exhibit a DBA for L = {xs | ∃ᶠ k, xs k = 1} (infinitely many 1s)
- Observe Lᶜ = eventuallyZero is not DBA-recognizable (existing result)
- Conclude DBAs are not closed under complement

This is still the simplest of the four main results, but it is not a one-liner.

### 6. Landweber's Theorem Forward Direction Has an Unresolved Source Gap (Teammate C; High confidence)

Thomas 2003 Thm 3.32 (forward direction, F closed under superloops → DBA-recognizable)
leaves the reset condition undefined: "until a F-loop is reached or outnumbered." The
standard interpretation is: reset when the accumulated set `R ∪ {q'}` contains some
`F ∈ accept` as a subset (i.e., is a superloop of an F-loop). This is implementable
given `[Fintype State] [DecidableEq State]`, but requires the implementor to fill the gap
explicitly. The backward direction (DBA-recognizable → F closed under superloops) uses
`ωSequence.flatten` with segment concatenation and is adequately sketched in the source.

### 7. Landweber Theorem Signature Requires `[DecidableEq S]` (Teammate C; High confidence)

The proposed signature with only `[Finite S]` is a concrete type error. The forward
construction builds a DBA over state space `State × Finset State`, which requires
`[Fintype State] [DecidableEq State]` (or at minimum `[Finite State] [DecidableEq State]`)
for `Finset` operations. Analogously, `BuchiCompl.lean` uses `[Fintype State] [DecidableEq State]`.

Corrected signature:

```lean
theorem DA.Muller.dba_recognizable_iff_closedUnderSuperloops
    [Fintype State] [DecidableEq State] (a : DA.Muller State Symbol) :
    (∃ acc : Set State, ωAcceptor.language (DA.Buchi.mk a.toDA acc) = ωAcceptor.language a) ↔
    a.ClosedUnderSuperloops
```

### 8. No SCC Infrastructure Exists for DBA; Loop Must Be Defined from Scratch (Teammates A, C; High confidence)

Mathlib's `Quiver.IsStronglyConnected` applies to the entire quiver type, not to subsets of
states. Adapting it would require creating a `Quiver` instance on the subtype `{s : State // s ∈ S}`
with the restricted transition relation — more bridging work than defining `IsLoop` directly.
The recommended approach (from both A and C) is:

```lean
def DA.IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, w ≠ [] ∧ da.mtr s w = s'
```

Teammate D adds the forward-looking recommendation: define `IsLoop` on the base `DA` type
(not on `DA.Muller`) so the predicate is reusable for future Rabin characterizations in task 252.

### 9. `infOcc` Needs Additional Lemmas for Landweber (Teammate B; High confidence)

The `infOcc` predicate in `InfOcc.lean` has four existing lemmas but is missing several
needed for Landweber:

| Needed lemma | Purpose |
|---|---|
| `infOcc_finite [Finite α]` | infOcc of finite-type ω-sequence is finite |
| `infOcc_nonempty_of_finite [Finite α]` | Pigeonhole: some state always recurs |
| `mem_infOcc` | Unfold characterization of membership |
| `infOcc_prod_run_fst` | infOcc of product run projects to component |

These additions target `InfOcc.lean` and are ~30-50 lines total.

### 10. DBA → DMA Conversion Belongs in Task 243 (Teammates C, D; High confidence)

`DA.Buchi.toMuller` is a method on the DBA type and is needed by task 241 (McNaughton).
Deferring it to task 252 creates an unnecessary dependency (task 252 is `[NOT STARTED]` and
has a large scope). The conversion itself is ~15-25 lines. Teammate C reinforces this
finding, noting that Phase 3 deferral "creates unnecessary coupling."

---

## Conflicts Resolved

### Conflict 1: Is Thomas 2003 Ch. 3 a "Complete Proof" for Landweber's Forward Direction?

**Tension**: Teammate A and the prior survey (Report 01) both state Thomas 2003 provides
"COMPLETE PROOF in both directions." Teammate C identifies a concrete gap: the forward
direction's reset condition ("outnumbered") is undefined.

**Resolution**: Teammate C's position is correct. Thomas 2003 provides an adequate proof
sketch, not a complete formal proof. The backward direction is essentially complete (uses
segment concatenation, which `ωSequence.flatten` covers). The forward direction requires
the implementor to define the reset predicate independently and prove the infOcc
characterization (~50-80 additional lines not covered by the text). The "complete proof"
claim in the prior survey is an overstatement; implementors should plan for additional
proof development beyond what the text suggests.

**Confidence in resolution**: High — Teammate C quotes the exact text with the gap and
explains the standard interpretation needed to fill it.

### Conflict 2: Is `DA.prod_run_eq` Formulated as Pointwise or as `ωSequence.zip`?

**Tension**: Teammate A states the lemma as `(da1.prod da2).run xs n = (da1.run xs n, da2.run xs n)`
(pointwise, with an `n : ℕ` argument). Teammate B formulates it as
`(da1.prod da2).run xs = (da1.run xs).zip (da2.run xs)` (ωSequence equality).

**Resolution**: Both are equivalent and either works. The pointwise form (Teammate A) is
marginally preferred because: (a) it has a `@[simp]` tag that works naturally with `simp`,
(b) the existing `prod_mtr_eq` is also pointwise (takes `s : State1 × State2`), and (c)
it avoids needing to prove `ωSequence.zip` properties. Both teammates agree on the
induction proof strategy.

### Conflict 3: Is DBA Complement Non-Closure "Essentially Free"?

**Tension**: Teammate A (and the prior survey) characterize this as "essentially free"
with "high" confidence and "almost entirely reuses existing CSLib infrastructure."
Teammate C identifies that a concrete 2-state DBA must still be constructed and its
correctness proved (~30-40 lines).

**Resolution**: Teammate C is correct that the proof is not free, but Teammate A is correct
that it is the simplest of the four results. The resolution is: "straightforward but not
trivial" — 30-40 lines of new code, mostly the DBA construction and a short computation
verifying it accepts exactly the correct language. Confidence in the proof strategy remains
High; only the effort estimate is corrected.

### Conflict 4: Line Count Estimates for BuchiInter.lean Baseline

**Tension**: The prior survey and Teammate A's estimates use ~350 lines as the baseline for
NBA intersection complexity. Teammate C measured the actual file: 137 lines.

**Resolution**: 137 lines is the correct baseline. Teammates A and B have not corrected
their absolute estimates (which are based on bottom-up analysis rather than scaling from
the NBA file), so their estimates of 150-200 lines for DBA intersection and 300-400 lines
for Landweber should be evaluated on their own merits, not by comparison to the NBA file.
Teammate C's revised Landweber estimate (500-700 lines) is based on bottom-up analysis
of the proof steps and is more reliable.

### Conflict 5: `frequently_or_distrib` vs `frequently_in_finite_type` for DBA Union

**Tension**: Teammate B initially notes uncertainty about which Mathlib lemma covers the
union proof key step, mentioning both `frequently_or_distrib` and `frequently_in_finite_type`
as candidates and suggesting the latter may be needed. Teammate C explicitly identifies
`Filter.frequently_or_distrib` as already present in `Mathlib.Order.Filter.Basic` (line 836)
and already used in `BuchiInter.lean` (line 111), making it sufficient without pigeonhole.

**Resolution**: `Filter.frequently_or_distrib` is sufficient. Teammate C's finding supersedes
Teammate B's uncertainty. The union proof does not require a separate pigeonhole argument.

---

## Construction Details

### Construction 0: `DA.prod_run_eq` (Prerequisite)

**Target file**: `Cslib/Computability/Automata/DA/Prod.lean` (extend existing file)

**Lean 4 type signature** (agreed by A, B, C):
```lean
@[simp]
theorem DA.prod_run_eq (da1 : DA State1 Symbol) (da2 : DA State2 Symbol)
    (xs : ωSequence Symbol) (n : ℕ) :
    (da1.prod da2).run xs n = (da1.run xs n, da2.run xs n)
```

**Proof strategy**: Induction on `n`. Base case: both sides are `(da1.start, da2.start)` by
`run_zero`. Inductive step: unfold `run_succ` and `FLTS.prod.tr`, apply IH.

**Known difficulties**: None. This is a trivial equational lemma.

**Estimated lines**: ~10

**Status**: Not in CSLib; must be added before any product-based DBA proof.

---

### Construction 1: DBA Union

**Target file**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (new file)

**Lean 4 type signatures** (Teammate A, validated by B and C):
```lean
def DA.Buchi.union (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2) Symbol where
  toDA := a₁.toDA.prod a₂.toDA
  accept := (a₁.accept ×ˢ Set.univ) ∪ (Set.univ ×ˢ a₂.accept)

theorem DA.Buchi.union_language_eq {a₁ : DA.Buchi State1 Symbol} {a₂ : DA.Buchi State2 Symbol} :
    ωAcceptor.language (a₁.union a₂) = ωAcceptor.language a₁ ⊔ ωAcceptor.language a₂
```

**Proof strategy**:
- Unfold acceptance: `∃ᶠ k in atTop, (run₁ k, run₂ k) ∈ (F₁ ×ˢ univ) ∪ (univ ×ˢ F₂)`
- Rewrite membership as disjunction: `run₁ k ∈ F₁ ∨ run₂ k ∈ F₂`
- Apply `Filter.frequently_or_distrib` (already in Mathlib, already imported)
- Use `DA.prod_run_eq` to decompose `(da₁.prod da₂).run xs n`

**Known difficulties** (Teammate C): Only the missing `DA.prod_run_eq` is a genuine obstacle.
Once that lemma is in place, the proof is essentially one `simp` with `frequently_or_distrib`.

**Estimated lines**: ~80-120 (including the definition and the language equality theorem)

---

### Construction 2: DBA Intersection

**Target file**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (same file as union)

**Lean 4 type signatures** (Teammate A, supported by B; counter choice confirmed by C):
```lean
noncomputable def DA.Buchi.inter (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol) :
    DA.Buchi (State1 × State2 × Fin 3) Symbol where
  tr := fun (s₁, s₂, c) x =>
    let s₁' := a₁.tr s₁ x
    let s₂' := a₂.tr s₂ x
    (s₁', s₂', DA.Buchi.interCounterTr a₁ a₂ s₁' s₂' c)
  start := (a₁.start, a₂.start, 0)
  accept := Set.univ ×ˢ Set.univ ×ˢ {(2 : Fin 3)}

theorem DA.Buchi.inter_language_eq {a₁ : DA.Buchi State1 Symbol} {a₂ : DA.Buchi State2 Symbol} :
    ωAcceptor.language (a₁.inter a₂) = ωAcceptor.language a₁ ⊓ ωAcceptor.language a₂
```

The counter transition function:
```lean
def DA.Buchi.interCounterTr (a₁ : DA.Buchi State1 Symbol) (a₂ : DA.Buchi State2 Symbol)
    (s₁ : State1) (s₂ : State2) (c : Fin 3) : Fin 3 :=
  match c with
  | 0 => if s₁ ∈ a₁.accept then 1 else 0
  | 1 => if s₂ ∈ a₂.accept then 2 else 1
  | 2 => if s₁ ∈ a₁.accept then 1 else 0
```

**Proof strategy** (merged from A and B):
- Forward: counter hits 2 infinitely often → between consecutive visits to 2, the counter
  cycled 0 → 1 → 2, meaning F₁ was visited (advancing 0 → 1) and F₂ was visited (advancing
  1 → 2). Hence both accepting conditions hold infinitely often.
- Backward: if F₁ visited infinitely often and F₂ visited infinitely often, the counter
  must cycle through all three states infinitely often. From state 0 it will eventually see
  F₁ (advance to 1); from state 1 it will eventually see F₂ (advance to 2).
- Use temporal reasoning from `OmegaSequence/Temporal.lean` (`LeadsTo`, `until_frequently_*`)
  as in the NBA intersection proof template.

**Known difficulties** (Teammate C):
- No `DA.addHist` exists; the counter transition must be inlined (Option 1: inline in
  `BuchiClosure.lean`; Option 2: define new `DA.addHist` infrastructure). Inline is
  recommended for this task.
- The `noncomputable` annotation is required (membership check requires `Classical.em`).
- Correctness proof is more complex than the union proof; follows the NBA intersection
  proof structure but without nondeterministic existentials.

**Estimated lines**: ~150-200 (counter definition ~30-40 lines, language equality ~120-160 lines)

---

### Construction 3: DBA Complement Non-Closure

**Target file**: `Cslib/Computability/Automata/DA/BuchiClosure.lean` (same file)

**Lean 4 type signatures** (Teammates A and B agree on structure; C corrects effort):
```lean
-- 2-state DBA for "infinitely many 1s" (must be explicitly constructed)
def DA.Buchi.infOftenOne : DA.Buchi (Fin 2) (Fin 2) where
  tr := fun _ x => x        -- transition to the symbol itself (0-state = last symbol was 0)
  start := 0
  accept := {(1 : Fin 2)}

-- Language correctness for the witness DBA
theorem DA.Buchi.infOftenOne_language_eq :
    ωAcceptor.language DA.Buchi.infOftenOne = {xs | ∃ᶠ k in atTop, xs k = 1}

-- Main non-closure result
theorem DA.Buchi.not_closed_complement :
    ∃ (Symbol : Type) (L : ωLanguage Symbol),
      (∃ S (da : DA.Buchi S Symbol), ωAcceptor.language da = L) ∧
      ¬ ∃ S (da : DA.Buchi S Symbol), ωAcceptor.language da = Lᶜ
```

**Proof strategy**:
- Witness: L = {xs | ∃ᶠ k, xs k = 1} (infinitely many 1s)
- L is DBA-recognizable: exhibited by `infOftenOne`
- Lᶜ = eventuallyZero: use `Filter.not_frequently` and `Fin.eq_zero_or_one`
- eventuallyZero is not DBA-recognizable: `IsRegular.not_da_buchi` (already in CSLib)

**Known difficulties** (Teammate C): The concrete DBA construction and its correctness proof
are not in CSLib and must be written (~30-40 lines). The non-recognizability direction is
already proved.

**Estimated lines**: ~60-80 total (DBA construction ~30-40 lines, main theorem ~20-40 lines)

---

### Construction 4: Landweber's Theorem

**Target file**: `Cslib/Computability/Automata/DA/BuchiChar.lean` (new file)

**New definitions required** (Teammates A, B, C agree; D adds future-proofing advice):

```lean
-- IsLoop defined on base DA (not DA.Muller) for reuse in future Rabin characterization
-- (Teammate D recommendation, supported by Teammate A's IsLoop' formulation)
def DA.IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
  S.Nonempty ∧ ∀ s ∈ S, ∀ s' ∈ S, ∃ w : List Symbol, w ≠ [] ∧ da.mtr s w = s'

def DA.Muller.ClosedUnderSuperloops (a : DA.Muller State Symbol) : Prop :=
  ∀ F ∈ a.accept, ∀ F' : Set State, a.toDA.IsLoop F' → F ⊆ F' → F' ∈ a.accept
```

**Main theorem type signature** (corrected per Teammate C):
```lean
theorem DA.Muller.dba_recognizable_iff_closedUnderSuperloops
    [Fintype State] [DecidableEq State] (a : DA.Muller State Symbol) :
    (∃ acc : Set State, ωAcceptor.language (DA.Buchi.mk a.toDA acc) = ωAcceptor.language a) ↔
    a.ClosedUnderSuperloops
```

Note: the `[Finite State]`-only constraint in the prior survey and Teammate A's proposal is
insufficient. `[Fintype State] [DecidableEq State]` is required (per Teammate C; analogous
to `BuchiCompl.lean`'s constraints).

**Proof strategy** (from Thomas 2003, with Teammate C's gap filled):
- Forward direction (ClosedUnderSuperloops → DBA-recognizable):
  1. Construct DBA `A'` with state space `State × Finset State`, start `(a.start, ∅)`
  2. Accumulate visited states: `R' := R ∪ {q'}` after each transition
  3. Reset condition: reset `R := ∅` when `R ∪ {q'}` contains some `F ∈ a.accept` as a
     subset (i.e., is a superloop of an F-loop). This is the definition of the reset that
     Thomas 2003 leaves as "outnumbered."
  4. Accepting states: `{(q, ∅)}`; `A'` accepts iff resets happen infinitely often
  5. Key lemma: resets happen infinitely often ↔ infOcc of the run is a superloop of some
     F-loop, which by ClosedUnderSuperloops implies infOcc ∈ accept

- Backward direction (DBA-recognizable → ClosedUnderSuperloops):
  1. Given DBA `B` recognizing `language a`; take `F ∈ accept`, superloop `F' ⊇ F`
  2. Construct ω-word: find `q ∈ F` reachable by `w`; cycle through `F` via `γ` (so `A`
     accepts `wγ`)
  3. Interleave `F' \ F` states: `wu₁v₁x₁u₂v₂x₂...` where `u_i` visits `B`'s final states,
     `v_i` cycles through `F` back to `q`, `x_i` traverses `F'`
  4. This ω-word is accepted by both `A` (infOcc = `F'`) and `B` (visits F_B infinitely)
  5. Therefore `F' ∈ accept`
  6. Uses `ωSequence.flatten` (available in `OmegaSequence/Flatten.lean`)

**Known difficulties** (Teammate C, Medium confidence):
- Forward direction reset condition is not in Thomas 2003; must be independently derived
- Key infOcc lemmas are missing from `InfOcc.lean` (see Prerequisites section)
- `Finset State` requires `[DecidableEq State]` throughout the DBA construction
- Line count is substantially larger than prior estimates: **500-700 lines** (not 300-400)

**Estimated lines**: 500-700 total for the full theorem (definitions ~60-80, forward
direction ~200-300, backward direction ~150-200, helper lemmas ~80-120)

---

### Construction 5: DBA → DMA Conversion

**Target file**: `Cslib/Computability/Automata/DA/BuchiChar.lean` (same file as Landweber,
or a short separate `DA/BuchiToMuller.lean`)

**Lean 4 type signatures**:
```lean
def DA.Buchi.toMuller (a : DA.Buchi State Symbol) : DA.Muller State Symbol where
  toDA := a.toDA
  accept := {S | S ∩ a.accept ≠ ∅}    -- Muller family: sets that hit accept

theorem DA.Buchi.toMuller_language_eq (a : DA.Buchi State Symbol) :
    ωAcceptor.language a.toMuller = ωAcceptor.language a
```

**Proof strategy**: The Muller automaton accepts `xs` iff `infOcc(run xs) ∩ a.accept ≠ ∅`
iff `∃ᶠ k, run xs k ∈ a.accept` (which is exactly DBA acceptance). Connect via
`infOcc` definition and `frequently_in_finite_type`.

**Known difficulties**: None significant. Straightforward once `infOcc` membership is
well-characterized.

**Estimated lines**: ~15-25

---

## Prerequisites Identified

Before the main constructions, the following must be in place:

| Item | Target file | Effort | Required by |
|------|-------------|--------|-------------|
| `DA.prod_run_eq` (ω-level product run) | `DA/Prod.lean` | ~10 lines | Union, Intersection |
| `infOcc_finite [Finite α]` | `InfOcc.lean` | ~10 lines | Landweber, toMuller |
| `infOcc_nonempty_of_finite [Finite α]` | `InfOcc.lean` | ~10 lines | Landweber |
| `mem_infOcc` (unfold lemma) | `InfOcc.lean` | ~5 lines | Landweber |
| `DA.IsLoop` definition | `BuchiChar.lean` | ~20-30 lines | Landweber |
| `DA.Muller.ClosedUnderSuperloops` | `BuchiChar.lean` | ~10-15 lines | Landweber |
| 2-state DBA for "infinitely many 1s" | `BuchiClosure.lean` | ~30-40 lines | Complement non-closure |

The `infOcc` prerequisite lemmas should be contributed to `InfOcc.lean` early (they are
broadly useful) and are approximately 25-30 lines total.

---

## Phase Ordering

### Phase 1: DBA Closure Properties (target: `DA/BuchiClosure.lean`)

**Step 0** (Prerequisites): Add `DA.prod_run_eq` to `DA/Prod.lean`. Add `infOcc_finite`,
`infOcc_nonempty_of_finite`, `mem_infOcc` to `InfOcc.lean`.

**Step 1**: DBA union — `DA.Buchi.union` definition and `union_language_eq` theorem

**Step 2**: DBA complement non-closure — construct `infOftenOne` DBA, prove
`infOftenOne_language_eq`, prove `not_closed_complement`

**Step 3**: DBA intersection — `interCounterTr` function, `DA.Buchi.inter` definition,
`inter_language_eq` theorem

Total Phase 1 estimated lines: ~300-420 (including prerequisites)

### Phase 2: DBA Characterization (target: `DA/BuchiChar.lean`)

**Step 1**: Define `DA.IsLoop` and `DA.Muller.ClosedUnderSuperloops`

**Step 2**: Prove auxiliary lemmas (`isLoop_iff_infOcc`, reset condition lemmas)

**Step 3**: Prove Landweber backward direction (DBA-recognizable → ClosedUnderSuperloops)
using `ωSequence.flatten` construction

**Step 4**: Prove Landweber forward direction (ClosedUnderSuperloops → DBA-recognizable)
by constructing the `State × Finset State` DBA

**Step 5**: Combine into `DA.Muller.dba_recognizable_iff_closedUnderSuperloops`

**Step 6**: Add `DA.Buchi.toMuller` and `toMuller_language_eq` (can be in same file or
`BuchiToMuller.lean`)

Total Phase 2 estimated lines: ~515-725

### Phase Ordering Rationale (Teammate D)

- Phase 1 can PR independently and creates immediate value
- Phase 2 stacks on Phase 1 (Landweber backward direction uses the loop + infOcc
  infrastructure established in Phase 1's prerequisites)
- Two-PR strategy is recommended: PR 1 = BuchiClosure.lean, PR 2 = BuchiChar.lean +
  BuchiToMuller.lean
- DBA → DMA conversion belongs in Phase 2 / task 243, NOT deferred to task 252

---

## Gaps and Risks

### Remaining Unknowns

1. **Landweber forward direction proof complexity**: The reset condition derivation and
   the infOcc characterization are the hardest steps. The 500-700 line estimate has
   medium confidence; actual effort could be higher if the `infOcc` interaction with
   `Finset State` accumulation requires significant additional lemmas.

2. **`ωSequence.flatten` interface**: The backward direction of Landweber uses segment
   concatenation. Teammate C confirms `ωSequence.flatten` exists in CSLib, but the exact
   API for constructing an ω-word from infinitely many finite segments should be verified
   before starting Phase 2.

3. **DBA intersection proof length**: Teammate A estimates 150-200 lines; there is no
   independent calibration. The NBA intersection is 137 lines with `addHist` abstractions;
   without those abstractions, the DBA version may run longer. Medium confidence on estimate.

4. **Thomas 2003 Landweber forward direction**: Requires a more formal reference to
   supplement the incomplete sketch. Teammate C suggests Perrin & Pin 2004 §5.3 or
   Staiger 1983, but both are behind paywalls. The implementor must be prepared to derive
   the reset condition independently.

5. **Classification Hierarchy (Thomas §3.6)**: Both reports 01 and D mention this as a
   high-value addition. It is explicitly out of scope for the current implementation phases
   but would strengthen the contribution. The lower half (`DBA ⊊ DMA`) is witnessed by
   `not_da_buchi`; the upper half (`E ⊊ DBA`) requires a new example.

6. **Complement Lemma 3.26b (DBA ↔ co-DBA by swapping accept)**: Teammate C notes this
   ~30-line corollary is omitted from scope. It is defensible to defer but worth noting
   as a low-effort high-value addition if time permits.

### Risks

| Risk | Severity | Mitigation |
|------|----------|------------|
| Landweber forward direction exceeds 700 lines | Medium | Split into sub-phases; use `sorry_inventory` to track open stubs |
| `infOcc` + `Finset` interaction requires unexpected lemmas | Medium | Validate `infOcc_nonempty_of_finite` early against `Finite.exists_infinite_fiber` |
| DBA intersection proof needs temporal lemmas not yet verified | Medium-Low | Check `Temporal.lean` API before starting intersection proof |
| `[DecidableEq State]` propagation through Landweber construction | Low | Use `open scoped Classical` or add `[DecidableEq]` explicitly at definition sites |

---

## Strategic Recommendations

(Synthesized from Teammate D; supported by Teammate C)

1. **Two-PR strategy**: Submit Phase 1 (`BuchiClosure.lean`) first as a self-contained PR.
   Submit Phase 2 (`BuchiChar.lean`) as a stacked PR. This separates the straightforward
   closure results from the complex characterization theorem in reviewer attention.

2. **Lead with Landweber in PR descriptions**: Frame PR 2 as "foundational infrastructure
   for McNaughton (task 241)." The `toMuller` conversion from Phase 2 provides the easy
   half of `IsRegular.iff_da_muller`. This framing will resonate with CSLib reviewers.

3. **Define `IsLoop` on the base `DA` type**: Not on `DA.Muller`. This makes the predicate
   reusable for future Rabin characterizations (task 252). The `ClosedUnderSuperloops`
   property is then stated about `a : DA.Muller` but references `a.toDA.IsLoop`.

4. **File layout** (from Teammate D, supported by all teammates):
   ```
   Cslib/Computability/Automata/DA/
   ├── Basic.lean          (existing)
   ├── Buchi.lean          (existing)
   ├── Prod.lean           (existing; add prod_run_eq)
   ├── Congr.lean          (existing)
   ├── ToNA.lean           (existing)
   ├── BuchiClosure.lean   ← NEW (Phase 1)
   ├── BuchiChar.lean      ← NEW (Phase 2; Landweber + DBA→DMA)
   └── [BuchiToMuller.lean] ← optional separate file for toMuller
   ```

5. **DBA → DMA in task 243**: `DA.Buchi.toMuller` must not be deferred to task 252.
   Task 241 (McNaughton) depends on it and task 252 is `[NOT STARTED]` with a large scope.

6. **Supplement the literature for Landweber forward direction**: Thomas 2003's proof sketch
   is a starting point, not a complete specification. The implementor should treat the reset
   condition as an independently-derived predicate and document it clearly in the Lean docstring.

7. **Architecture boundary**: Keep DA/ and NA/ closure properties in separate files.
   `OmegaRegularLanguage.lean` is the correct integration layer where DBA results become
   `IsRegular.*` statements.

8. **Forward pointer**: Add a docstring cross-reference in the Landweber theorem to
   `BuchiCompl.lean` (task 250), noting that Landweber's theorem gives the exact condition
   under which DBA fails, explaining why rank-based NBA complementation is necessary.

---

## Teammate Contributions

| Teammate | Angle | Status | Confidence |
|----------|-------|--------|------------|
| A | Primary constructions with Lean 4 signatures | Completed | High (union, complement, prod_run_eq); Medium (intersection); Medium-Low (Landweber) |
| B | Alternative approaches and reuse opportunities | Completed | High (NBA non-reuse, infOcc gaps, `frequently_or_distrib` uncertainty); Medium (Landweber Muller formulation) |
| C | Critical review: gaps and proof difficulties | Completed | High (all findings verified against source) |
| D | Strategic horizons and PR strategy | Completed | High (two-PR strategy, file layout, DBA→DMA placement); Medium (architecture recommendations) |

---

## References

- Thomas 2003, "Automata and Reactive Systems" (RWTH Aachen lecture notes)
  - Ch. 1: Product intersection construction with counter trick
  - Ch. 3: Landweber's Theorem (Thm 3.32) — forward direction incomplete, backward direction
    adequate. Classification hierarchy (§3.6). Complement Lemma (Lemma 3.26b).
- Baier & Katoen 2008, *Principles of Model Checking*
  - Theorem 4.50: DBA < NBA (used in `IsRegular.not_da_buchi`)
  - Exercises 4.22-4.23: DBA complement non-closure and union closure hints
- CSLib prior research: `specs/243_deterministic_buchi_automata/reports/01_dba-constructions-survey.md`
- Mathlib: `Filter.frequently_or_distrib` (Order.Filter.Basic line 836)
- CSLib: `IsRegular.not_da_buchi` (`Languages/OmegaRegularLanguage.lean` lines 61-69)
- CSLib: `buchi_eq_finAcc_omegaLim` (`DA/Buchi.lean`)
- CSLib: `DA.prod`, `DA.prod_mtr_eq` (`DA/Prod.lean`)
- CSLib: `NA.BuchiInter.lean` (137 lines; proof pattern template for intersection)
- CSLib: `BuchiCompl.lean` (~275 lines; scale reference for complex DBA proofs)
- CSLib: `ωSequence.flatten` (`OmegaSequence/Flatten.lean`; needed for Landweber backward)
