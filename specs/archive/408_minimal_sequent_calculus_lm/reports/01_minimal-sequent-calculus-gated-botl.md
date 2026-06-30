# Research Report 01: Minimal Sequent Calculus via a Property-Gated `botL`

**Task**: 408 — Minimal sequent calculus / `LM` (Wave 5 of task 407 redesign)
**Session**: sess_1782760056_06c853_408
**Date**: 2026-06-29
**Status**: researched
**Source**: task 407 report 01 §3.4/§7 (W5), report 02 §6; in-source design note `NaturalDeduction/Basic.lean:44–115`

---

## 1. Executive summary

The **PRIMARY design is feasible** and is the recommended route. A single single-conclusion
sequent-calculus inductive parameterized by a theory `T : Theory Atom`, with the `botL`
constructor gated by `[IsIntuitionistic T]`, lets MPL and IPL be the *same inductive at
different property strengths*. The structural metatheory (cut elimination, subformula
property) is then proved **once** generically over `T`, and `LJProof.cutElim`,
`LJProof.sound`, `hilbert_iff_lj`, etc. are recovered by instantiating at `T = IPL`.

This is the exact analogue, one layer down, of the gated `efq` already shipped in
`Theory.Derivation` (task 398/407 W1). The gate mechanism is **verified to compile** in
Lean (four MCP `lean_run_code` checks below), including the cut-elimination–critical pattern
of *reconstructing* `botL` inside a recursive branch.

The cost is a **mechanical, well-scoped refactor**: every `match`/`induction` arm that
touches `botL` (~36 sites across the six LJ files) must use the `@`-qualified constructor
pattern, and every site that *reconstructs* `botL` must add one `letI := inst` line. No
proof is restructured; `termination_by sizeOf …` is unaffected.

The **FALLBACK** (a separate `LMProof` inductive = LJ minus `botL`) is *not recommended*:
because `LJProof` would then be a distinct inductive, LJ's cut elimination cannot literally
re-use `LM`'s — the `botL` arms (trivial leaves) must be re-done anyway, and the entire
inductive + `height`/`mono`/`CutFree`/`cutElim` signatures are duplicated. It is strictly
*more* code than the gated approach and diverges from the ND layer. Keep it only as an
escape hatch if a future obstruction in the gated proof appears (none found here).

**Zero-debt note**: no `sorry`, no new axiom, no vacuous definition is required or
recommended. The refactor is structural and preserves every existing theorem.

**Zulip AI policy** (407 report 02, msg #605827029): any Zulip reply must be human-authored.
This report and any in-source docstrings are internal artifacts and are unaffected; do not
post LLM-drafted prose to Zulip.

---

## 2. Ground truth: the current code

### 2.1 The hard-coded `botL` (the gap)

`LJProof` (`SequentCalculus/LJ/Basic.lean:86–135`) is **not** parameterized by a theory; its
`botL` is an unconditional leaf:

```lean
inductive LJProof : @Sequent Atom → Type u where
  | ax (A) (Γ) (_ : A ∈ Γ) : LJProof (Γ ⊢ A)
  | botL (Γ) (C) (_ : (⊥ : Proposition Atom) ∈ Γ) : LJProof (Γ ⊢ C)   -- lines 91–92
  | andL … | andR … | orL … | orR1 … | orR2 … | impL … | impR …
  | weakL … | cut …
```

`LKProof` (`LK/Basic.lean:70–123`) is structurally identical with a multiple-conclusion
succedent and its own unconditional `botL` (lines 76–77).

Structural metatheory is proved **per system**: `LJ/CutElimination.lean` (712 lines),
`LJ/SubformulaProperty.lean`, `LJ/Decidability.lean`, `LJ/Interpolation.lean`, and the parallel
`LK/*`. This duplicates the entire Hauptsatz architecture across LJ and LK and gives no
`⊥`-free base. (407 report 01 §3.4 calls this "the largest structural gap".)

### 2.2 The pattern to mirror: gated `efq` in ND

`Theory.Derivation` (`NaturalDeduction/Basic.lean:146–183`) is parameterized by
`{T : Theory Atom}` and gates explosion:

```lean
inductive Theory.Derivation {T : Theory Atom} : Ctx Atom → Proposition Atom → Type u where
  | ax … | ass … | andI … | … | impE …
  | efq {Γ} {A} [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A   -- lines 182–183
```

with `MPL := (∅ : Theory)` (`Defs.lean:154`), `IPL := Set.range (Proposition.imp ⊥ ·)`
(`Defs.lean:157`), and the gate class

```lean
class IsIntuitionistic (T : Theory Atom) where
  efq (A : Proposition Atom) : (⊥ → A) ∈ T          -- Defs.lean:166–167
instance instIsIntuitionisticIPL : IsIntuitionistic IPL                 -- Defs.lean:182
```

The gate-free fragment is *named* (not a new inductive) by `IsBotRuleFree`
(`Basic.lean:223–235`, `efq ↦ False`) and `MinimalDerivation := MPL.Derivation`
(`Basic.lean:242`). The same Curry–Howard term language gates its `abort`
(`CurryHoward/Defs.lean:103`) and *reconstructs* it under reduction
(`CurryHoward/Reduction.lean:166`). This is the template task 408 should reproduce at the
sequent layer.

---

## 3. Goal 2 — Does Lean permit a typeclass-gated sequent constructor? (VERIFIED YES)

Yes — a constructor may carry an instance-implicit binder `[IsIntuitionistic T]`, exactly as
`Derivation.efq` does. **No** predicate/side-condition parameter is needed. The one
non-obvious requirement, confirmed by direct experiment, concerns how the instance is
recovered when **pattern-matching** the gated constructor:

- The anonymous-dot pattern `.botL _ _ _` does **not** work: the equation compiler tries to
  *synthesize* `IsIntuitionistic T` (which fails for a generic `T`), rather than *binding* the
  stored instance. Error: `failed to synthesize instance … IsIntuitionistic T`.
- The fix is the `@`-qualified pattern, which binds **every** field including the instance:
  - read-only consumer arm: `| _, @SeqProof.botL _ _ _ _ _ => …`
  - reconstruction arm (term mode): `| _, _, @SeqProof.botL _ _ C inst hbot, h => letI := inst; .botL …`
  - reconstruction arm (tactic `induction`): `| @botL Γ C inst hbot => letI := inst; …`

### 3.1 Verification log (MCP `lean_run_code`)

A faithful scale model (`class IsInt`, `structure Sqt`, `inductive SProof (T : Nat)` with a
gated `botL [IsInt T]`, plus `ax`/`weakL`) was checked. The final consolidated snippet
compiled with **no errors** on all four definitions (the only diagnostic was a cosmetic
`Prop`/`Type` mismatch in a throwaway `#check` tuple and an unused-variable lint):

| Pattern exercised | Mirrors LJ site | Result |
|---|---|---|
| `SProof.size` (read-only, `@SProof.botL _ _ _ _ _ => 0`) | `LJProof.height`, `LJCutFree` | compiles |
| `SProof.IsBotFree` (`@SProof.botL … => False`) | `IsBotRuleFree` analog | compiles |
| `SProof.relocate` (term recursion, reconstruct `botL` in new ctx via `letI := inst`) | `LJProof.mono`, every cut-adm helper | compiles |
| `SProof.dup` (tactic `induction … with | @botL Γ C inst hbot => letI := inst; …`) | `LJProof.cutElim` botL arm | compiles |

The decisive fact: **every `botL` reconstruction in the LJ proofs happens inside a branch
that just matched a `botL`**, so the `[IsIntuitionistic T]` instance is always in hand to
rebuild it. No site ever needs to synthesize the instance from nothing. This is why the
gate composes with the existing Hauptsatz unchanged.

---

## 4. Goal 1 & 3 — Cut elimination under the gate (FEASIBLE; hard cases identified)

### 4.1 Why `botL` is structurally harmless to cut elimination

In the existing LJ Hauptsatz (`LJ/CutElimination.lean`), `botL` is treated as a **zero-premise
leaf** in every helper. It is never a non-trivial principal formula requiring the
subformula induction hypothesis `LJCutIH`:

- In the three principal helpers (`ljCutAdm_principal_andR/orR/impR`), the `botL` arm simply
  rebuilds `botL` in the relocated context (lines 137–138, 248–249, 368–369). No `ih` call.
- In `ljCutAdm_left` (line 475–476) the `botL` arm rebuilds `botL Γ₀ C₀`. No `ih` call.
- In `ljCutAdm_right` the only place `botL` interacts with the cut formula is when the **cut
  formula itself is `⊥`** (lines 558–564): `if heq : (⊥ : Proposition Atom) = A`. It delegates
  to `ljCutAdm_left` with a freshly built `botL`; again no subformula `ih`, because `⊥` has no
  proper subformulas and `botL` has no premises.

Consequently **gating `botL` changes none of the recursion or termination structure**. The
`termination_by sizeOf d₂` / `sizeOf d₁` / `sizeOf A` measures are untouched: `sizeOf` of a
gated constructor application is identical. The proof goes through generically over `T`.

### 4.2 The "hard cases" — they are mechanical, not mathematical

There is **no mathematically hard case** introduced by gating. The only work is mechanical
and enumerable. `botL` reconstruction sites in `LJ/CutElimination.lean` (13 occurrences of
`botL`) each become:

```lean
-- before
| .botL _ _ hbot, _ => ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) nofun), …⟩
-- after
| _, _, @SeqProof.botL _ _ _ inst hbot, _ =>
    letI := inst
    ⟨.botL Γ₀ _ (ljMem_of_ne_head (hant hbot) nofun), …⟩
```

and the `ljCutAdm_right` `⊥`-cut arm (line 558) likewise gains a `letI := inst` before its two
`botL` constructions. The `LJProof.cutElim` tactic arm (line 678) becomes
`| @botL Γ C inst hbot => letI := inst; exact ⟨⟨.botL Γ C hbot, trivial⟩⟩`.

### 4.3 What is generic vs. strength-specific

- **Generic over `T` (proved once)**: `height`, `mono`, `CutFree` predicate, `cutAdmissibility`,
  `cutElim`, subformula property. These never depend on `IsIntuitionistic T` except to
  rebuild a matched `botL`, which is always available.
- **Strength-specific (stay at `T = IPL`)**: soundness and completeness. `LJProof.sound`
  (`LJ/Soundness.lean:53–64`) targets **intuitionistic Kripke** models where the `botL` arm
  discharges via `IForces v (fun _ => False) w ⊥ = False` (Soundness.lean:46). That argument
  requires `⊥` to be false, i.e. the *intuitionistic* reading — it is genuinely not generic
  over MPL (where `⊥` is an ordinary proposition). Likewise `hilbert_iff_lj`
  (`LJ/Completeness.lean:278`) is keyed to `IntPropAxiom`. These are **recovered unchanged**
  by defining `LJProof := SeqProof IPL`, so the gated constructor is constructible and the
  proofs are byte-for-byte the same modulo the `@botL`/`letI` cosmetic.

This is precisely the task's intent: "structural metatheory proved ONCE generically over the
gate", soundness/completeness remain per-strength.

---

## 5. Recommended PRIMARY design (concrete module map)

### 5.1 The single inductive (new `SequentCalculus/Basic.lean` or extend `Defs.lean`)

```lean
namespace Cslib.Logic.PL
open Proposition Theory
variable {Atom : Type u} [DecidableEq Atom]

/-- Single-conclusion sequent proofs over a theory `T`. The ten connective/structural rules
are ungated (MPL base); `botL` (explosion) is the gated property module, available exactly
when `[IsIntuitionistic T]`. MPL = `SeqProof ∅` (no `botL`); IPL = `SeqProof IPL`. -/
inductive SeqProof (T : Theory Atom) : @Sequent Atom → Type u where
  | ax (A) (Γ) (_ : A ∈ Γ) : SeqProof T (Γ ⊢ A)
  | botL (Γ) (C) [IsIntuitionistic T] (_ : (⊥ : Proposition Atom) ∈ Γ) : SeqProof T (Γ ⊢ C)
  | andL … | andR … | orL … | orR1 … | orR2 … | impL … | impR … | weakL … | cut …
```

(`T` is used *only* in the `botL` gate; the sequent `ax` is identity-based, `A ∈ Γ`, not
theory-based — see Open Question Q1 on whether to carry full `T` or a lighter phantom carrier.
Recommendation: carry `T : Theory Atom` for one-to-one parity with `Theory.Derivation`.)

### 5.2 Names, fragments, and recovery

```lean
/-- Minimal-strength sequent calculus (no `botL`). -/
abbrev SeqProofMinimal (Γ : Ctx Atom) (C : Proposition Atom) := SeqProof MPL (Γ ⊢ C)

/-- Gate-free fragment predicate (mirrors `Derivation.IsBotRuleFree`); `botL ↦ False`. -/
def SeqProof.IsBotRuleFree : SeqProof T seq → Prop | … | @SeqProof.botL .. => False | …

/-- LJ recovered: IPL strength makes `botL` constructible, preserving all results. -/
abbrev LJProof (seq : @Sequent Atom) : Type u := SeqProof IPL seq
```

Then `LJProof.height`, `LJProof.mono`, `LJCutFree`, `CutFreeLJProof`, `ljCutAdmissibility`,
`LJProof.cutElim` are each **either** the generic `SeqProof.*` specialized to `IPL`, **or**
thin `@[deprecated]`-free re-exports preserving the exact public type. Soundness, completeness,
subformula, decidability, interpolation files import `SeqProof`, keep their statements about
`LJProof = SeqProof IPL`, and change only `botL` match cosmetics.

### 5.3 LK is out of scope for unification (per task)

LK is multiple-conclusion (`LKSequent`, two-sided), a different structural shape. The task
explicitly keeps LK its own calculus "related via its own module rather than folded in." LK's
`botL` *may* optionally be gated the same way for internal consistency (a `SeqProofLK T`), but
that is **not required** by 408 and should not block it. Recommend: leave `LKProof` untouched
in this task; note the parallel gating as future work. Preserve `LKProof.cutElim`,
`hilbert_iff_lk`, `CutFreeCompleteness` verbatim.

---

## 6. Goal 4 — The FALLBACK, concretely evaluated (not recommended)

Define `LMProof` with the 10 non-`botL` constructors; prove `cutElim`/subformula on `LMProof`;
"recover LJ = LM + botL by composition/re-export."

**Why it costs more, not less:**

1. `LJProof` remains (or becomes) a *separate* inductive that includes `botL`. LM's
   `cutElim` is a theorem about `LMProof`, a different type — it cannot be the proof of
   `LJProof.cutElim`. You need an embedding `LMProof ↪ LJProof` and then an *LJ-level* cut
   elimination that still discharges the `botL` arms. Those arms are exactly the trivial
   leaves of §4.2 — so they must be written **anyway**, with none of the saving the gate gives.
2. The whole inductive plus `height`, `mono`, `CutFree`, `CutFreeLMProof`, and the
   cut-admissibility helper *signatures* are duplicated between `LM` and `LJ`.
3. It diverges from the ND layer (which uses one gated inductive + `IsBotRuleFree`/
   `MinimalDerivation`), reintroducing exactly the two-inductive duplication 407 set out to
   remove (407 report 01 §3.4, report 02 §6 option C).

**When to fall back**: only if a concrete obstruction blocks the gated cut-elimination proof.
The MCP experiments (§3.1) found none — the gate is inert to the recursion. So the fallback is
documented for completeness but should not be planned as the path.

---

## 7. Goal 6 — Results that MUST be preserved (no weakening)

External consumers fix the public surface that may not change type:

| Symbol | Defined | External consumer |
|---|---|---|
| `LJProof` (Nonempty in TFAE) | LJ/Basic | `ProofSystemEquivalence.lean:84–105` |
| `LJProof`, `CutFreeLJProof`, `LJProof.cutElim`, `hilbert_iff_lj` | LJ/Basic, CutElim, Completeness | `Semantics/Algebra/OrImpConservative.lean:35–184` |
| `LJProof.sound` | LJ/Soundness:53 | LJ barrel |
| subformula property, `LJProof.height`, `LJProof.mono`, `LJCutFree` | LJ/* | internal |
| `LKProof`, `LKProof.cutElim`, `hilbert_iff_lk`, LK cut-free completeness | LK/* | keep entirely |

Preservation strategy: `LJProof := SeqProof IPL` (abbrev) keeps `Nonempty (LJProof …)` and
`induction` on `LJProof` working; `CutFreeLJProof`, `LJCutFree`, `LJProof.cutElim`,
`hilbert_iff_lj`, `LJProof.sound` are re-exported with identical signatures (generic theorem
specialized to `IPL`, or a one-line wrapper). `OrImpConservative.lean` does
`induction dp : LJProof seq` and pattern-matches constructors incl. `botL` — those arms must be
audited for the `@botL` cosmetic (3 `botL` occurrences there).

---

## 8. Goal 5 — API/patterns and Lean code sketches

- **Gate class & strengths already exist**: `IsIntuitionistic` / `MPL` / `IPL`
  (`Defs.lean:154–183`); `instIsIntuitionisticExtention` (Defs.lean:190) lets any
  `T ⊇ IPL` count as intuitionistic — so `SeqProof CPL` also has `botL`.
- **Mathlib `Finset` API** used throughout is unchanged: `Finset.insert_subset_insert`,
  `Finset.subset_insert`, `Finset.mem_of_mem_insert_of_ne` (wrapped as `ljMem_of_ne_head`,
  CutElimination.lean:110). No new Mathlib lemmas required.
- **Verified gate template** (the load-bearing snippet; reproduce at LJ scale):

```lean
-- read-only consumer
def SeqProof.height : SeqProof T seq → Nat
  | .ax _ _ _ => 0
  | @SeqProof.botL _ _ _ _ _ => 0          -- @-pattern binds the instance field
  | …
-- reconstruction (term mode)
  | _, _, @SeqProof.botL _ _ C inst hbot, h => letI := inst; .botL Γ' C (h hbot)
-- reconstruction (tactic induction)
  | @botL Γ C inst hbot => letI := inst; exact ⟨⟨.botL Γ C hbot, trivial⟩⟩
```

- **Reuse-first check (CSLib)**: searched `Cslib.Logics.Propositional.*`. No existing minimal
  sequent calculus, no `LM` module, no generic `SeqProof`. The gate primitives
  (`IsIntuitionistic`, `MPL`, `IPL`, `MinimalDerivation`, `IsBotRuleFree`) already exist in
  `Defs.lean`/`NaturalDeduction/Basic.lean` and should be reused directly — do **not** define
  new gate classes.

---

## 9. Risks, constraints, zero-debt

- **Mechanical breadth, not depth**: ~36 `botL` match arms across six LJ files (Basic 8,
  CutElimination 13, Interpolation 9, Soundness 2, Subformula 2, Completeness 2) plus
  `OrImpConservative.lean` (3). Each is a local `@`-pattern (+`letI` when rebuilding). High
  count, low individual difficulty — size the plan by file, build-green per file.
- **`set_option maxHeartbeats 400000`** already on `ljCutAdm_right` (CutElimination.lean:541) —
  keep; the gate adds no compile cost.
- **`@[expose] public section`** semantics and the `InferenceSystem` instance
  (`LJ/Basic.lean:211`) must be re-pointed to `SeqProof IPL`.
- **Zero-debt**: achievable with no `sorry`/axiom/vacuous def. If, contrary to the
  experiments, a specific cut-elim arm resists the gate, mark that phase `[BLOCKED]` for user
  review rather than introducing `sorry` — but none is anticipated.
- **Zulip AI policy**: human-authored prose only for any Zulip post; docstrings/report are
  internal and fine.

---

## 10. Open questions for the planner

1. **Carrier of the gate**: parameterize `SeqProof` by full `T : Theory Atom` (ND parity,
   recommended) vs. a lighter phantom/`[Explosion]` carrier, given the sequent `ax` does not
   use `T`. Parity with `Theory.Derivation` argues for `T : Theory Atom`.
2. **Naming/placement**: `SeqProof` in a new `SequentCalculus/Basic.lean`, with `LJProof :=
   SeqProof IPL` kept in `LJ/Basic.lean`? Or generic helpers in `LJ/Basic.lean` directly?
3. **LK**: gate LK's `botL` symmetrically now (cheap, consistent) or defer (task says defer)?
4. **`SeqProofMinimal`/`IsBotRuleFree` parity** with task 409 (ND `⊥`-rule-free inductive) —
   coordinate naming so the two layers read the same.

---

## 11. Recommendation

Proceed with the **PRIMARY gated-`botL` design**. It is verified feasible, matches the ND
layer's shipped pattern, proves the structural Hauptsatz once over `T`, preserves every LJ/LK
result by `LJProof := SeqProof IPL` + re-export, and unifies MPL/IPL with zero duplication. The
work is a file-scoped mechanical refactor; recommend a `--hard`, per-file-green
implementation plan. Reserve the FALLBACK only for an unforeseen obstruction.
