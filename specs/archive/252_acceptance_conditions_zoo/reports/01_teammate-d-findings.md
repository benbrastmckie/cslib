# Teammate D Findings: Strategic Horizons for Task 252

**Role**: Horizons — long-term alignment and strategic direction
**Artifact**: 01_teammate-d-findings.md
**Task**: 252 — Formalize Rabin and parity acceptance conditions in CSLib

---

## Key Findings

### 1. Task 252 Fits the Computability Layer, Not the Logic Layer

CSLib has a clean separation between its two major subsystems:

- `Cslib/Computability/Automata/` — ω-automata infrastructure (DBA, DMA, NBA, NA, Emptiness, BuchiCompl, etc.)
- `Cslib/Logics/` — modal, temporal, bimodal, LTL, HML logics

Task 252 belongs entirely to the Computability layer. There is no direct dependency path from
tasks 39/40 (temporal completeness) into the Computability/Automata code. The temporal logics
at `Cslib/Logics/Temporal/` do not import from `Cslib/Computability/Automata/` at all —
that import direction only exists for `Cslib/Logics/LTL/`, which imports from
`Cslib/Computability/Automata/NA/`. This separation is intentional and should be preserved.

### 2. The Direct Predecessor in the Acceptance Condition Chain Is Already Present

`DA/Basic.lean` already defines `DA.Buchi` and `DA.Muller` with the `ωAcceptor` instance
pattern. `DA/BuchiChar.lean` has the `IsLoop` predicate declared explicitly as "reusable for
future Rabin characterizations (task 252)" — a direct architectural affordance left by the
current contributors. `infOcc` in `Foundations/Data/OmegaSequence/InfOcc.lean` supplies the
"infinitely often" core that Rabin and parity acceptance conditions require.

The existing code anticipates task 252. The `IsLoop` definition is already scoped at the base
`DA` level precisely so it can be reused across Buchi, Muller, Rabin, and Parity contexts.

### 3. The Strategic Chain Is: Rabin/Parity → McNaughton (241) → Model Checking

The key downstream dependency chain is:

```
Task 252 (Rabin + Parity + conversions)
  → Task 241 (McNaughton: IsRegular.iff_da_muller)
    → IsRegular.iff_da_parity (free corollary via conversion chain)
      → Future: μ-calculus / parity games model checking
```

`OmegaRegularLanguage.lean` has `proof_wanted IsRegular.iff_da_muller` as the McNaughton
theorem stub. Once task 252 provides Muller↔Rabin and Rabin↔Parity conversions, task 241
gains a canonical three-way equivalence: `IsRegular ↔ DMA ↔ DRA ↔ DPA`. This is the
complete ω-automata equivalence picture. The `IsRegular.iff_da_parity` corollary (DPA
characterization of ω-regular languages) then becomes accessible as a free theorem from
the conversion chain once McNaughton is proved for DMA.

The LTL model checking theorem at `Cslib/Logics/LTL/ModelChecking.lean` currently uses
NBA. A parity-based model checking path (NBA → DPA via Piterman) would be a natural
long-term extension, though it is not presently in scope.

### 4. Tasks 39/40 (Temporal Completeness) Are Architecturally Independent of Task 252

Tasks 39 (discrete temporal completeness) and 40 (continuous temporal completeness) operate
entirely in the Hilbert proof-system / canonical-model paradigm. They work with:
- `Cslib/Logics/Temporal/Metalogic/` (MCS, Soundness, Completeness, Chronicle construction)
- `Cslib/Foundations/Logic/Metalogic/` (generic MCS infrastructure)

Neither path goes through automata theory. There is no technical dependency between
task 252 and tasks 39/40 — they operate in fully separate stacks. Attempting to scope
task 252 to advance tasks 39/40 would be a category error.

The only indirect connection is conceptual: the LTL omega-language regularity theorem
(in `OmegaRegular.lean`) and the LTL model checking theorem (in `ModelChecking.lean`) are
on a trajectory that touches automata theory, while temporal completeness is on a
canonical-model trajectory. These are distinct threads.

### 5. The Minimal Viable Scope Is Well-Defined and Self-Contained

The task description is already well-scoped for a PR:

- **Phase 1**: `DA/Rabin.lean` — `DA.Rabin` structure, acceptance predicate using `infOcc`
  (Inf(ρ) ∩ Eᵢ = ∅ ∧ Inf(ρ) ∩ Fᵢ ≠ ∅ for some i)
- **Phase 2**: `DA/Parity.lean` — `DA.Parity` structure, priority coloring, min-even acceptance
- **Phase 3**: `DA/Conversions.lean` — Muller↔Rabin, Rabin→Parity, Parity→Rabin

This is roughly 3 new files in the pattern of `BuchiChar.lean` (which is ~180 lines for
DBA→DMA plus Landweber). Estimated total: 400-600 lines. The nondeterministic variants
(NA.Rabin, NA.Parity) are optional stretch goals, not required for the core PR.

### 6. Streett Acceptance Is a Natural Inclusion at Minimal Cost

The Streett condition uses the same pair structure as Rabin (it is the dual: for ALL i,
if Inf ∩ Fᵢ ≠ ∅ then Inf ∩ Eᵢ ≠ ∅). Since Rabin pairs are already being defined,
adding `DA.Streett` with a dual acceptance predicate and a Rabin↔Streett duality theorem
costs roughly 30-50 additional lines and provides the fairness-constraint interpretation
widely used in verification. The seed report lists it as optional but it has clear payoff.

### 7. The `proof_wanted` Convention Matches This Work's Status

`BuchiChar.lean` already shows how CSLib handles partially-proved major theorems:
`Muller.dba_recognizable_implies_closedUnderSuperloops`,
`Muller.closedUnderSuperloops_implies_dba_recognizable`, and
`Muller.dba_recognizable_iff_closedUnderSuperloops` are all `proof_wanted`. Task 252
should follow the same pattern: define the types and acceptance predicates fully, prove
the direction of each conversion that is mechanically straightforward (e.g., Parity→Rabin
via k/2 pairs is a direct construction), and leave the harder direction of Rabin→Parity
(Piterman 2007) as `proof_wanted` if the state-machine construction is too large for a
single PR. The definitions + easy conversions + `proof_wanted` stubs constitute a
shippable, zero-sorry contribution.

---

## Recommended Approach

### Scope for the PR

**Include in task 252**:
1. `DA.Rabin` type + `ωAcceptor` instance (Rabin pairs acceptance)
2. `DA.Parity` type + `ωAcceptor` instance (min-even priority coloring)
3. `DA.Streett` type + `ωAcceptor` instance (dual of Rabin, ~30 extra lines)
4. Muller↔Rabin conversion (polynomial in Muller table size) — fully proved
5. Büchi→Rabin trivial embedding (1 pair, E₁=∅) — fully proved
6. Parity→Rabin direct construction (k/2 pairs) — fully proved
7. Rabin→Parity construction (Piterman 2007) — structure + `proof_wanted` for correctness
8. Rabin↔Streett duality — fully proved (complement pairs, trivial)

**Leave for future tasks**:
- NBA→DPA (Safra/Piterman) — this is the full determinization theorem, not a conversion
- NA.Rabin, NA.Parity nondeterministic variants — natural follow-on
- IsRegular.iff_da_rabin, IsRegular.iff_da_parity — depends on task 241 (McNaughton first)

### Connection to Task 241 (McNaughton)

Task 252 should add a comment in `OmegaRegularLanguage.lean` noting that once
`IsRegular.iff_da_muller` (McNaughton) is proved, the conversion chain in `Conversions.lean`
immediately gives `IsRegular.iff_da_rabin` and `IsRegular.iff_da_parity` as corollaries.
This documents the dependency without blocking task 252 on task 241.

### File Organization

Follow the existing `DA/` pattern:

```
Cslib/Computability/Automata/DA/
  Basic.lean         (existing — DA, DBA, DMA types)
  Buchi.lean         (existing — buchi_eq_finAcc_omegaLim)
  BuchiChar.lean     (existing — IsLoop, DBA→DMA, Landweber proof_wanteds)
  BuchiClosure.lean  (existing — DBA closure properties)
  Rabin.lean         (NEW — DA.Rabin, DA.Streett, Rabin↔Streett duality)
  Parity.lean        (NEW — DA.Parity with priority coloring)
  Conversions.lean   (NEW — Muller↔Rabin, Rabin↔Parity, Büchi→Rabin)
```

All three new files import from `DA/Basic.lean` and
`Foundations/Data/OmegaSequence/InfOcc.lean`. Conversions.lean imports Rabin.lean and
Parity.lean.

### Zero-Debt Strategy

The Piterman 2007 Rabin→Parity construction involves an exponential-state automaton
(O(n · k!) states). The construction is a ranked tree traversal over Rabin pairs; it
is mechanically complex to verify but structurally clear. The recommended approach is:

1. Define the state type for the Piterman construction fully (it is a pair of a Rabin
   state and a permutation of Rabin pairs).
2. Define the transition and acceptance condition.
3. Prove the language inclusion in one direction (easier: parity → rabin accepts implies
   parity accepts) — this is straightforward from the construction.
4. Leave the other direction (rabin accepts implies parity accepts) as `proof_wanted` with
   a complete proof sketch following Piterman 2007 Section 3.

This pattern matches exactly what `BuchiChar.lean` does for Landweber's theorem.

---

## Evidence / Examples

### Evidence 1: `IsLoop` Is Pre-Positioned for Rabin

`DA/BuchiChar.lean` line 54-56:
```lean
/-- A set `S` of states of a `DA` is a *loop* if it is nonempty and for every pair of
states `s s' ∈ S`, there exists a nonempty word `w` such that `da.mtr s w = s'`.

Defined on the base `DA` type (not `DA.Muller`) so the predicate is reusable for future
Rabin characterizations (task 252). -/
def IsLoop (da : DA State Symbol) (S : Set State) : Prop :=
```

The comment explicitly references task 252. This is an architectural affordance.

### Evidence 2: `infOcc` Is the Foundation for All Four Acceptance Conditions

`DA/Basic.lean` line 116-118:
```lean
instance : ωAcceptor (Muller State Symbol) Symbol where
  Accepts (a : Muller State Symbol) (xs : ωSequence Symbol) :=
    (a.run xs).infOcc ∈ a.accept
```

Rabin acceptance can be stated as:
```lean
instance : ωAcceptor (Rabin State Symbol) Symbol where
  Accepts (a : Rabin State Symbol) (xs : ωSequence Symbol) :=
    ∃ i, (a.run xs).infOcc ∩ (a.pairs i).fst = ∅ ∧
         ((a.run xs).infOcc ∩ (a.pairs i).snd).Nonempty
```

The `infOcc` predicate is already the right primitive.

### Evidence 3: McNaughton's Theorem Stub Awaits the Conversion Chain

`OmegaRegularLanguage.lean` line 261-264:
```lean
/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p
```

Once task 252 provides `DA.Muller ↔ DA.Rabin ↔ DA.Parity` conversions, task 241 fills
this `proof_wanted`, and all three DxA characterizations of ω-regular languages fall out.

### Evidence 4: LTL Model Checking Uses NBA, Not DPA (Yet)

`LTL/ModelChecking.lean` uses `gnbaNBA` (generalized non-deterministic Büchi automaton)
for model checking. There is no current parity-based model checking path. Parity acceptance
is a future extension, not a present dependency.

### Evidence 5: Temporal Completeness Is Architecturally Isolated from Automata

`Cslib/Logics/Temporal/Metalogic/Completeness.lean` and its Chronicle pipeline have no
imports from `Cslib/Computability/Automata/`. The proof-system completeness pipeline
(MCS → Lindenbaum → canonical model → truth lemma → counterexample) is entirely
self-contained in the logic layer. Tasks 39 and 40 cannot be advanced by task 252.

---

## Confidence Level

| Claim | Confidence |
|-------|-----------|
| Task 252 fits Computability layer, not Logic layer | High — confirmed by import analysis |
| No dependency between task 252 and tasks 39/40 | High — import graph shows zero overlap |
| `IsLoop` is pre-positioned for Rabin reuse | High — explicit comment in BuchiChar.lean |
| Muller↔Rabin can be fully proved (no proof_wanted) | Medium — standard construction, moderate complexity |
| Piterman Rabin→Parity should be proof_wanted | Medium-High — state machine complexity warrants deferral |
| Streett is worth including at minimal cost | Medium — 30-50 lines, clear payoff for fairness use case |
| Task 252 → 241 → IsRegular.iff_da_parity is the right chain | High — follows from conversion composition |
| μ-calculus / parity games is a future destination | Medium — not yet in CSLib scope, but natural target |

---

## Summary

Task 252 is a well-scoped, architecturally clean addition to CSLib's computability layer.
It completes the ω-automata acceptance condition zoo (Büchi → Muller → Rabin → Parity)
that the existing `DA/Basic.lean` and `DA/BuchiChar.lean` infrastructure anticipates.
The correct strategic framing is:

1. Task 252 delivers the four acceptance condition types plus mutual conversions.
2. Task 241 uses the Muller type from task 252's conversion chain to prove McNaughton.
3. IsRegular.iff_da_rabin and IsRegular.iff_da_parity become free corollaries.
4. Parity acceptance positions CSLib for future μ-calculus and parity games work.

Tasks 39 and 40 (temporal completeness) are on an entirely separate trajectory and
cannot be advanced by task 252. The scope should not be stretched to attempt that
connection — it does not exist architecturally.
