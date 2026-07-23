# Research Report: Minimal Sequent Calculus (LM) and Three-Way MPL TFAE

**Task**: 547 — Close the (SequentCalculus, Minimal) hole in the proof-system × logic matrix.
**Goal**: Add a minimal-logic sequent calculus mirroring the LJ tree, prove soundness against
minimal Kripke semantics, completeness, and Hilbert-equivalence, then extend the two-way
`mplHilbertIffNd` to a symmetric three-way `mplProofSystemsTfae`. Zero sorry.

---

## 1. Executive Summary (Reuse-First Finding — READ THIS FIRST)

**The minimal sequent-calculus *rules* already exist in CSLib.** The task description's premise
that "no minimal sequent calculus exists in CSLib" is **stale**. The core `SeqProof` inductive in
`Cslib/Logics/Propositional/SequentCalculus/LJ/Basic.lean` is **already generic over a theory
`T : Theory Atom`**, and the minimal calculus is **already defined**:

```lean
abbrev SeqProofMinimal (seq : @Sequent Atom) : Type u := SeqProof MPL seq   -- LJ/Basic.lean:154
```

The explosion rule `botL` is **gated** by `[IsIntuitionistic T]`. Since `MPL = ∅` admits no
`IsIntuitionistic` instance, `botL` is **structurally unconstructible** at minimal strength — this
is exactly "LJ minus ex falso" that the task asks for. The right rules (`orR1`/`orR2`, `impR`,
`andR`) are already single-conclusion and already minimal-safe. **No new rule inductive is
needed.** The following also come free, already generic over `T` and therefore instantiable at
`MPL`:

| Already generic over `T` (reuse directly at `MPL`) | Location |
|---|---|
| `SeqProof` (rules), `SeqProof.height`, `SeqProof.mono` | LJ/Basic.lean:94, 157, 181 |
| `SeqProof.CutFree`, `SeqProof.IsBotRuleFree` | LJ/Basic.lean:222, 238 |
| `SeqProof.formulas` (subformula infrastructure) | LJ/SubformulaProperty.lean:51 |

**Consequence for scope**: the LM/ directory is NOT a from-scratch rebuild of the LJ tree. The
real new work is three thin files — a naming/re-export `Basic`, a `Soundness` against the minimal
Kripke semantics (arbitrary `bot_forces`), and a `Completeness` (ND→LM translation) — plus the
TFAE extension. The entire semantic completeness backend (`min_soundness`, `min_strong_completeness`,
`min_soundness_completeness`) and the Hilbert–ND bridge (`hilbert_iff_nd_ctx_min`) already exist
sorry-free.

**Critical technical risk RESOLVED by verification (Section 6)**: induction over `SeqProof MPL`
generates a `botL` case carrying a hypothetical `[IsIntuitionistic MPL]` instance; this discharges
cleanly. A live `lean_run_code` check compiled the soundness skeleton (including the hardest
`impR` case over arbitrary `bot_forces`) with the `botL` case closed by
`exact absurd (by assumption) not_isIntuitionistic_mpl`.

---

## 2. Path Correction

The task cites `Propositional/Metalogic/ProofSystemEquivalence.lean:19`. The actual file is at
**`Cslib/Logics/Propositional/ProofSystemEquivalence.lean`** (not under `Metalogic/`). The stale
claim is at **lines 19–20 and 116**:

```
19  propositional logic, stated as `List.TFAE` theorems. For minimal logic (MPL), only a
20  two-way Hilbert–ND equivalence is available (no minimal sequent calculus exists in CSLib).
...
116 No minimal sequent calculus (LM) exists in CSLib, so only a two-way equivalence is available.
```

These docstrings must be updated as part of the implementation.

---

## 3. Target Architecture (Mirror of LJ)

Existing LJ tree (`SequentCalculus/LJ/`): `Basic`, `Soundness`, `Completeness`, `CutElimination`,
`SubformulaProperty`, `Interpolation`, `Decidability`, plus barrel `LJ.lean`.

Proposed LM tree (`SequentCalculus/LM/`) — **only what the TFAE requires**:

| New file | Content | Mirrors |
|---|---|---|
| `LM/Basic.lean` | `abbrev LMProof := SeqProofMinimal`; helper `not_isIntuitionistic_mpl`; `LMCutFree`/`CutFreeLMProof` re-exports (optional) | LJ/Basic.lean (but ~30 lines, mostly re-export) |
| `LM/Soundness.lean` | `SeqProofMinimal.sound` / `lm_sound` against arbitrary `bot_forces`; corollary `lm_of_proof_mvalid` giving `MSemanticEntails` | LJ/Soundness.lean |
| `LM/Completeness.lean` | `lmOfMinAxiom` (8 axioms), `ndToLM`, `nd_iff_lm`, `hilbert_iff_lm`, `lm_iff_mvalid` | LJ/Completeness.lean |
| `LM.lean` | barrel import | LJ.lean |

**Out of scope for the TFAE (task-permitted to defer)**: `LM/CutElimination.lean`,
`LM/SubformulaProperty.lean`, `LM/Interpolation.lean`, `LM/Decidability.lean`. The task states cut
elimination "may follow the LJ development where applicable but is not required for the TFAE." Do
not build these unless a later roadmap task requests them. (Note the generic `SeqProof.CutFree` /
`mono` / `formulas` already exist at `MPL`, so a future LM cut-elimination task starts from
substantial reuse.)

Barrel/registration updates required:
- Add `public import ...SequentCalculus.LM` to `SequentCalculus.lean`.
- Run `lake exe mk_all --module` to update `Cslib.lean` (currently registers LJ at lines 574–581).

---

## 4. Key Type/Definition Reference (verified signatures)

- `Theory Atom := Set (Proposition Atom)`; `MPL : Theory := ∅`; `IPL := Set.range (imp ⊥ ·)`
  (Defs.lean:142,154,157).
- `class IsIntuitionistic (T) where efq : (⊥ → A) ∈ T`; `isIntuitionisticIff : IsIntuitionistic T ↔ IPL ⊆ T`
  (Defs.lean:166,171).
- `Ctx Atom := Finset (Proposition Atom)`; `Sequent := Ctx Atom × Proposition Atom`, notation `Γ ⊢ A`
  (NaturalDeduction/Basic.lean:128,135).
- `inductive Theory.Derivation {T} : Ctx → Proposition → Type` — 10 ungated rules +
  gated `| efq [IsIntuitionistic T] : Derivation Γ ⊥ → Derivation Γ A` (NaturalDeduction/Basic.lean:146–183).
- `MinPropAxiom` — **8 constructors, NO efq** (Axioms.lean:126–150); `IntPropAxiom` — 9 (adds efq).
- `AxiomTheory Axioms := {φ | Axioms φ}` (Equivalence.lean:85). Note `AxiomTheory MinPropAxiom` is
  **also not intuitionistic** (no `⊥→A`), so `Theory.Derivation`'s `efq` is unconstructible there too.
- `IForces v bot_forces w : Proposition → Prop`; `MValid` quantifies over arbitrary upward-closed
  `bot_forces`; `IValid` fixes `bot_forces = fun _ => False` (Kripke.lean:81,145,153).
- `iforces_persistence (v_uc) (bf_uc) (hw : w ≤ w') (hf) : IForces .. w' φ` (Kripke.lean:125).
- `MSemanticEntails Γ φ` — minimal Kripke consequence, arbitrary `bot_forces` (SemanticConsequence.lean:265).
- `MSemanticEntails_of_MValid` (SemanticConsequence.lean:290).

Pre-existing sorry-free backend (reuse verbatim):
- `min_soundness`, `min_soundness_derivable`, `min_completeness`, `min_soundness_completeness`
  (Metalogic/MinSoundness.lean, MinStrongCompleteness.lean).
- `min_strong_completeness : MSemanticEntails Γ φ → SetDerivable MinPropAxiom Γ φ`
  (MinStrongCompleteness.lean:257).
- `hilbert_iff_nd_ctx_min : Deriv MinPropAxiom Γ.toList φ ↔ DerivableIn (AxiomTheory MinPropAxiom) (Γ ⊢ φ)`
  (Equivalence.lean:448).

---

## 5. Lemma-by-Lemma Implementation Map (LJ → LM)

### 5.1 `LM/Soundness.lean` — mirror `LJProof.sound` (LJ/Soundness.lean:53)

Statement (generalize `bot_forces` from `fun _ => False` to an arbitrary upward-closed `bf`):

```lean
theorem SeqProofMinimal.sound {seq : @Sequent Atom} (d : SeqProofMinimal seq) :
    ∀ {World : Type*} [Preorder World]
      (v : World → Atom → Prop) (bf : World → Prop)
      (_ : ∀ {w w' : World} (p : Atom), w ≤ w' → v w p → v w' p)
      (_ : ∀ {w w' : World}, w ≤ w' → bf w → bf w')
      (w : World),
      (∀ B ∈ seq.1, IForces v bf w B) → IForces v bf w seq.2
```

Case map (induction on `d`):
- `ax`, `andL`, `andR`, `orL`, `orR1`, `orR2`, `impL`, `weakL`, `cut`: **identical** to
  `LJProof.sound`, just threading `bf`/`bf_uc` in place of `fun _ => False`. None of these cases
  inspect `bot_forces`, so they transfer verbatim (the LJ proof's `iforces_persistence` call in
  `impR` currently passes `(fun {_ _} h hf => absurd hf id)` for `bf_uc`; the LM version passes the
  real `bf_uc` — **strictly easier/more uniform**).
- `impR`: use `iforces_persistence v_uc bf_uc hw' (hant C hC)` — **verified compiling** (Section 6).
- `botL`: **discharge** via `exact absurd (by assumption) not_isIntuitionistic_mpl` — **verified**.

Corollary feeding completeness/TFAE (mirror `lj_sound`):
```lean
theorem lm_msemantic_entails {Γ : Ctx Atom} {A : Proposition Atom}
    (d : SeqProofMinimal (Γ ⊢ A)) : MSemanticEntails (↑Γ : Set _) A := ...
```

### 5.2 `LM/Completeness.lean` — mirror `LJ/Completeness.lean`

**(a) Axiom proofs** `lmAxiom…` — mirror `ljAxiom…` (LJ/Completeness.lean:71–167) but only the **8
MinPropAxiom** schemata. **Drop `ljAxiomEfq`** (it uses `SeqProof.botL`, unavailable at `MPL`).
Retained: `implyK, implyS, andI, andE1, andE2, orI1, orI2, orE`. Each is `botL`-free already (inspect
LJ source: only `ljAxiomEfq` uses `botL`), so they typecheck unchanged at `SeqProof MPL`.

**(b) Dispatch** `lmOfMinAxiom : MinPropAxiom φ → Nonempty (SeqProofMinimal (Γ ⊢ φ))` — mirror
`ljOfIntAxiom` (LJ/Completeness.lean:171) with 8 cases (no `efq` case).

**(c) ND→LM translation** `ndToLM` — mirror `ndToLJ` (LJ/Completeness.lean:193). Input is
`(AxiomTheory MinPropAxiom).Derivation Γ A`. Cases `ax, ass, andI, andE1, andE2, orI1, orI2, orE,
impI, impE` transfer directly (they use `cut`/`andL`/`orL`/`impL`, all `MPL`-available). The
`| efq` case (LJ/Completeness.lean:235, which uses `SeqProof.botL`) is **unconstructible** at
`AxiomTheory MinPropAxiom` and is discharged the same way (`absurd` on the uninhabited
`[IsIntuitionistic (AxiomTheory MinPropAxiom)]`). Noncomputable (Prop-valued axioms → `Classical.choice`).

**(d) Bridges** — mirror `nd_iff_lj`, `hilbert_iff_lj`, `lj_iff_ivalid`:
```lean
theorem nd_iff_lm {Γ A} :
    DerivableIn (AxiomTheory (@MinPropAxiom Atom)) (Γ ⊢ A) ↔ Nonempty (SeqProofMinimal (Γ ⊢ A))
-- →  via ndToLM
-- ←  via SeqProofMinimal.sound → MSemanticEntails → min_strong_completeness
--       → SetDerivable MinPropAxiom → (rw ← hilbert_iff_nd_ctx_min) → weakening
theorem hilbert_iff_lm {Γ φ} :
    Deriv MinPropAxiom Γ.toList φ ↔ Nonempty (SeqProofMinimal (Γ ⊢ φ)) :=
  hilbert_iff_nd_ctx_min.trans nd_iff_lm
theorem lm_iff_mvalid {φ} : MValid.{u,u} φ ↔ Nonempty (SeqProofMinimal (∅ ⊢ φ))
```

The backward direction of `nd_iff_lm` substitutes `int_strong_completeness`→`min_strong_completeness`
and `ISemanticEntails`→`MSemanticEntails`; structurally identical to `nd_iff_lj`
(LJ/Completeness.lean:253–270).

### 5.3 `ProofSystemEquivalence.lean` — extend two-way to three-way

Mirror `iplProofSystemsTfae` (lines 87–93). Replace/augment `mplHilbertIffNd` (line 118):

```lean
theorem mplProofSystemsTfae (Γ : Ctx Atom) (φ : PL.Proposition Atom) :
    [Deriv MinPropAxiom Γ.toList φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) (Γ ⊢ φ),
     Nonempty (SeqProofMinimal (Γ ⊢ φ))].TFAE := by
  tfae_have 1 ↔ 2 := hilbert_iff_nd_ctx_min
  tfae_have 2 ↔ 3 := nd_iff_lm
  tfae_finish

theorem mplProofSystemsTfaeClosed (φ : PL.Proposition Atom) :
    [Derivable MinPropAxiom φ,
     DerivableIn (AxiomTheory (@MinPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (SeqProofMinimal ((∅ : Ctx Atom) ⊢ φ))].TFAE := by
  have h := mplProofSystemsTfae (∅ : Ctx Atom) φ
  simp only [Finset.toList_empty] at h
  exact h
```

Retain `mplHilbertIffNd` for backward compatibility (or re-derive from the TFAE). Add
`public import Cslib.Logics.Propositional.SequentCalculus.LM.Completeness` and update the module
docstring + the stale lines 19–20 and 116. This makes the MPL row structurally symmetric with the
CPL (`LK`) and IPL (`LJ`) rows.

---

## 6. De-Risking Verification (live `lean_run_code`)

Compiled successfully (warnings only: unused `DecidableEq`, and the deliberate `sorry` for the
cases not under test):

```lean
theorem not_isIntuitionistic_mpl : ¬ Theory.IsIntuitionistic (∅ : Theory Atom) := by
  intro h
  have := (Theory.isIntuitionisticIff (∅ : Theory Atom)).mp h
  have hmem : (⊥ → ⊥ : Proposition Atom) ∈ (Theory.IPL : Theory Atom) := ⟨⊥, rfl⟩
  exact absurd (this hmem) (by simp)
```
- `botL` induction case closed by: `exact absurd (by assumption) not_isIntuitionistic_mpl`.
- `impR` case over **arbitrary** `bf` closed by `iforces_persistence v_uc bf_uc hw' (hant C hC)`.

This is the only case that differs materially from LJ; both confirmed. Remaining cases are literal
copies of the (already sorry-free) `LJProof.sound` arms. Confidence in a zero-sorry outcome: high.

Recommendation: place `not_isIntuitionistic_mpl` in `LM/Basic.lean` (add `omit [DecidableEq Atom]`
to silence the `unusedSectionVars`/`unusedDecidableInType` linters, or prove with `classical`).

---

## 7. Zero-Debt / Standards Compliance

- **No sorry / no new axioms / no vacuous defs.** Every obligation reduces to a copy of an existing
  sorry-free LJ arm or to the two verified minimal-specific discharges. No structural gap requires
  deferral. If any arm unexpectedly fails, escalate `[BLOCKED]` (do NOT insert sorry) per zero-debt gate.
- **Lint prevention** (weekly cron, not PR CI — fix proactively):
  - `docBlame`: every new `def`/`theorem` (`LMProof`, `lmAxiom…`, `ndToLM`, `nd_iff_lm`,
    `mplProofSystemsTfae`, …) needs a docstring. LJ files are the template.
  - `defLemma`: Prop-valued results (`…sound`, `nd_iff_lm`, `hilbert_iff_lm`, TFAE) use
    `theorem`; proof-tree *constructions* (`lmAxiom…`, `ndToLM`) stay `def`/`noncomputable def`
    (they build `Type`-valued proof terms, exactly as LJ does).
  - `defsWithUnderscore`: lowerCamelCase for defs (`lmOfMinAxiom`, `ndToLM`); snake_case theorem
    names (`nd_iff_lm`, `hilbert_iff_lm`, `lm_iff_mvalid`) follow the established LJ/mathlib mix
    already used in this codebase (`nd_iff_lj`, `hilbert_iff_lj`).
  - `unusedSectionVars` / `unusedDecidableInType`: use `omit [DecidableEq Atom] in` where a lemma
    (e.g. `not_isIntuitionistic_mpl`) does not need it — flagged live in Section 6.
- **CSLib file requirements**: every new file starts with `import Cslib.Init` then `module` /
  `@[expose] public section`; follow the exact header block used by LJ files. Copyright header
  matches existing files (Benjamin Brast-McKie, Apache 2.0).
- **CI order** before completion: `lake exe cache get` → `lake build` → `lake exe checkInitImports`
  → `lake lint` → `lake exe lint-style` → `lake exe mk_all --module` (new files) →
  `lake shake --add-public --keep-implied --keep-prefix`.

---

## 8. Suggested Phase Plan (for planner)

1. **Phase 1 — `LM/Basic.lean`**: `abbrev LMProof`, `not_isIntuitionistic_mpl` (+ `omit`), optional
   `LMCutFree`/`CutFreeLMProof` re-exports. Build-check.
2. **Phase 2 — `LM/Soundness.lean`**: `SeqProofMinimal.sound` (copy LJ arms, thread `bf`/`bf_uc`,
   discharge `botL`), `lm_msemantic_entails` corollary. Build-check.
3. **Phase 3 — `LM/Completeness.lean`**: 8 `lmAxiom…`, `lmOfMinAxiom`, `ndToLM`, `nd_iff_lm`,
   `hilbert_iff_lm`, `lm_iff_mvalid`. Build-check.
4. **Phase 4 — barrels + TFAE**: `LM.lean`; update `SequentCalculus.lean`; add
   `mplProofSystemsTfae`/`mplProofSystemsTfaeClosed` and fix stale docstrings in
   `ProofSystemEquivalence.lean`; `mk_all --module`; full CI pass.

Each phase is one agent run (~50–200 lines), bounded by the corresponding LJ file's size.

---

## 9. Scope Guard (from task)

- **Tableau stays OUT of the TFAE** (task 375 owns folding tableau into the TFAE). The MPL tableau
  system already exists at `Tableau/Minimal/` but must NOT be added as a 4th TFAE disjunct here.
- **LM cut elimination / subformula property / interpolation / decidability are NOT required** for
  the TFAE and should not be built in this task (may be spun off as follow-up roadmap items;
  generic `SeqProof` infrastructure at `MPL` gives them a strong starting point).

---

## 10. Open Questions / Notes for Planner

- **Naming**: `SeqProofMinimal` already exists in `LJ/Basic.lean`. Options: (a) reuse it directly
  everywhere and make `LM/Basic.lean` a pure re-export/discoverability alias `LMProof`; (b) keep
  `SeqProofMinimal` as the canonical name and have the TFAE reference it. Recommend (a) — an
  `abbrev LMProof := SeqProofMinimal` gives the mirror-symmetric surface name while reusing the
  existing generic machinery, consistent with reuse-first.
- **`mplHilbertIffNd`**: keep it (re-export) so existing references don't break; the new TFAE
  supersedes but does not replace it.
- The `ndToLM` `impE`/`andE`/`orE`/`impI` cases route through `SeqProof.cut`; LM is defined *with*
  `cut` (cut is not gated), so completeness needs no cut-elimination — matching how `ndToLJ` works.
