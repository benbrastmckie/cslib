# Research Report: Parametric Modal Completeness Cascade (Task 336)

**Task type**: cslib / lean4
**Session**: sess_1782319118_5be8e3_336
**Date**: 2026-06-24
**Mode**: read-only research

## 1. Summary

The 15 `Systems/*/Completeness.lean` files (3,205 lines total) each contain a
mechanically identical "completeness cascade" — `strong_soundness`,
`strong_completeness`, `strong_completeness_iff`, `compactness`,
`weak completeness` — differing only in three parameters: (a) the axiom
predicate + axiom-constructor callbacks, (b) the truth-lemma variant
(`truth_lemma` / `k_truth_lemma` / `d_truth_lemma`), and (c) the frame-condition
hypotheses. Task 335 already proved this refactor pattern works structurally for
soundness (shared `Satisfies.*_axiom` lemmas + parametric `soundness` in
`Metalogic/Soundness.lean`, with each system delegating). The completeness cascade
is a direct analogue.

The shared file `Metalogic/Completeness.lean` already defines the correct
abstraction `ModalSemanticEntails FC Γ φ` (a frame-class-parameterized semantic
entailment), but **only K uses it** — the other 14 systems inline the frame
conditions as ad-hoc `∀`-hypotheses. Unifying on `ModalSemanticEntails` with a
per-system `FC` predicate is the key enabling move.

**Recommendation**: add a parametric cascade (5 generic theorems) to
`Metalogic/Completeness.lean`, parameterized over `Axioms`, `FC`, the 4
propositional-axiom callbacks, a pre-applied `truthLemma` callback, and a
`canonical_FC` proof. Refactor all 15 systems to instantiate it. Estimated
reduction: ~1,300–1,600 lines, consistent with the task target.

## 2. Files and Line Inventory (verified)

| File | Lines | Role |
|------|------:|------|
| `Metalogic/Completeness.lean` | 568 | Shared infra (canonical model, frame lemmas, `truth_lemma`, `ModalSemanticEntails`, consistency lemmas). **Add cascade here.** |
| `Systems/K/Completeness.lean` | 367 | K-family truth-lemma infra (`k_derive_box_from_inconsistency`, `k_mcs_box_witness`, `k_truth_lemma`) + K cascade |
| `Systems/D/Completeness.lean` | 468 | D-family truth-lemma infra (`d_canonical_serial`, `d_mcs_box_witness`, `d_truth_lemma`) + D cascade |
| `Systems/{S4,S5,TB,T}/Completeness.lean` | 185/204/195/175 | T-family cascade only |
| `Systems/{B,K4,K5,K45,KB5}/Completeness.lean` | 169/159/159/172/180 | K-family cascade only (import K's infra) |
| `Systems/{D4,D5,D45,DB}/Completeness.lean` | 190/187/205/190 | D-family cascade only (import D's infra) |

The unique infra in K (lines 44–260) and D (lines 1–337) is **truth-lemma
machinery**, NOT cascade — the cascade portion of each is the last ~100 lines
(K: 262–367; D: 339–467). Those cascade portions are what gets replaced.

## 3. The Three Truth-Lemma Families (verified)

All three share `CanonicalModel`/`CanonicalWorld` from `Metalogic/Completeness.lean`
and produce the **same result type**:
`(φ : Proposition Atom) → (Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)`.

| Family | Truth lemma | Defined in | Extra axiom callback | Systems |
|--------|-------------|-----------|----------------------|---------|
| T-family | `truth_lemma` | `Metalogic/Completeness.lean` | `h_T` (modalT) | T, S4, S5, TB |
| K-family | `k_truth_lemma` | `Systems/K/Completeness.lean` | none beyond K | K, B, K4, K5, K45, KB5 |
| D-family | `d_truth_lemma` | `Systems/D/Completeness.lean` | `h_D` (modalD) | D, D4, D5, D45, DB |

Callback prefixes are uniform: all take `h_implyK, h_implyS, h_efq, h_peirce, h_K`;
T adds `h_T`, D adds `h_D`. **At the cascade call site the differences vanish** —
each is fully applied to its axiom callbacks BEFORE being threaded into the
cascade, yielding the uniform type above. The cascade therefore accepts a single
pre-applied `truthLemma` argument and is agnostic to family.

## 4. Frame-Condition Inventory (verified)

| System | Axiom pred | Frame condition hypotheses | Canonical proof(s) |
|--------|-----------|----------------------------|--------------------|
| K | `KAxiom` | `fun _ => True` | (trivial) |
| T | `TAxiom` | refl `∀ w, m.r w w` | `canonical_refl` |
| S4 | `S4Axiom` | refl + trans | `canonical_refl`, `canonical_trans` |
| S5 | `ModalAxiom` | refl + trans + eucl | `canonical_refl`, `canonical_trans`, `canonical_eucl` |
| TB | `TBAxiom` | refl + symm | `canonical_refl`, `canonical_symm` |
| B | `BAxiom` | symm | `canonical_symm` |
| K4 | `K4Axiom` | trans | `canonical_trans` |
| K5 | `K5Axiom` | eucl | `canonical_eucl_from_5` |
| K45 | `K45Axiom` | trans + eucl | `canonical_trans`, `canonical_eucl_from_5` |
| KB5 | `KB5Axiom` | symm + eucl | `canonical_symm`, `canonical_eucl_from_5` |
| D | `DAxiom` | `Relation.Serial m.r` | `d_canonical_serial` |
| D4 | `D4Axiom` | serial + trans | `d_canonical_serial`, `canonical_trans` |
| D5 | `D5Axiom` | serial + eucl | `d_canonical_serial`, `canonical_eucl_from_5` |
| D45 | `D45Axiom` | serial + trans + eucl | + all three |
| DB | `DBAxiom` | serial + symm | `d_canonical_serial`, `canonical_symm` |

**Key inconsistency to normalize**: frame conditions are currently inlined
differently. T/S4/S5/TB use raw `∀ w, m.r w w` / triple-`∀` conjuncts; D-family
uses `Relation.Serial m.r`; K uses `fun _ => True` via `ModalSemanticEntails`.
The shared `ModalSemanticEntails FC Γ φ` predicate (Completeness.lean:465–471)
with `FC : ∀ {World}, Model World Atom → Prop` accommodates all of these:
- K: `FC := fun _ => True`
- T: `FC := fun m => ∀ w, m.r w w`
- D: `FC := fun m => Relation.Serial m.r`
- S5: `FC := fun m => (∀ w, m.r w w) ∧ trans ∧ eucl`

Adopting `ModalSemanticEntails` uniformly removes the per-system bespoke
quantifier prose in all five cascade theorems and is the single largest source
of line savings.

## 5. The Cascade Structure (mechanically identical, verified across K/T/S5/D)

Five theorems per system. Body steps:

1. **`*_strong_soundness`**: `obtain ⟨L, hL_sub, ⟨d⟩⟩ := h` (unfold
   `ModalSetDerivable`), then `exact <sys>_soundness d m <frameconds> w
   (fun ψ hψ => h_sat ψ (hL_sub ψ hψ))`. Delegates to the per-system
   `*_soundness` already refactored in task 335.
2. **`*_strong_completeness`** (contrapositive): `by_contra h_not` →
   `modal_not_SetDerivable_union_neg_consistent (.implyK)(.implyS)(.efq)(.peirce) h_not`
   → `modal_lindenbaum h_cons` → derive `h_neg_phi`, `h_gamma_sub` →
   derive canonical frame properties via `canonical_*` callbacks →
   `h_gamma_sat` via `truthLemma … .mpr` → apply hypothesis `h` →
   `h_phi_M` via `truthLemma … .mp` → close with
   `mcs_bot_not_mem hM_mcs (modal_implication_property … h_neg_phi h_phi_M)`.
3. **`*_strong_completeness_iff`**: `⟨strong_completeness, strong_soundness⟩`.
4. **`*_compactness`**: `obtain ⟨L,…⟩ := strong_completeness h; exact ⟨L, …,
   strong_soundness ⟨L, …⟩⟩`.
5. **`*_completeness`** (weak): `ModalSetDerivable_empty_iff.mp
   (strong_completeness (ModalSemanticEntails_of_Valid … ∅))`.

Steps 2–5 are **character-identical** modulo the FC bundle, the axiom
constructors, and the truth-lemma symbol. K already realizes this cleanly using
`ModalSemanticEntails (fun _ => True)` (K/Completeness.lean:262–367) — it is the
ready-made template for the parametric version.

## 6. Reuse Check (CSLib reuse-first protocol)

- **`ModalSemanticEntails` / `ModalSemanticEntails_of_Valid`** — already in
  `Metalogic/Completeness.lean`. REUSE as the cascade's entailment vocabulary.
- **`ModalSetDerivable` / `ModalSetDerivable_empty_iff`** — already shared. REUSE.
- **`modal_not_SetDerivable_union_neg_consistent`, `modal_lindenbaum`,
  `mcs_bot_not_mem`, `modal_implication_property`** — already shared. REUSE.
- **`canonical_refl/trans/symm/eucl/eucl_from_5`** — already shared. REUSE as
  callbacks.
- **Task 335 soundness leg** — per-system `*_soundness` already delegates to
  parametric `soundness`; the cascade's `*_strong_soundness` calls those. REUSE.
- **No existing shared `strong_completeness`/`strong_soundness`/`compactness`** —
  confirmed absent from both `Soundness.lean` and `Completeness.lean`. This is
  the new code to add.
- **Mathlib**: `Relation.Serial` is the only Mathlib dependency in frame
  conditions; already used by the D-family. No new Mathlib lemmas required — the
  cascade is pure plumbing over existing CSLib infra.

## 7. Recommended Parameterization Strategy

Add to `Metalogic/Completeness.lean` (after `ModalSemanticEntails_of_Valid`):

**7.1 Parametric `strong_soundness`** (generic over `Axioms`, `FC`):

```
theorem strong_soundness {Axioms} {FC} {Γ} {φ}
    (sound : ∀ {World} (m : Model World Atom) (w : World), FC m →
        ModalSetDerivable Axioms Γ φ →  -- or a per-axiom soundness callback
        (∀ γ ∈ Γ, Satisfies m w γ) → Satisfies m w φ)
    (h : ModalSetDerivable Axioms Γ φ) :
    ModalSemanticEntails FC Γ φ
```

Note: cleanest is to thread the per-system `*_soundness` (the 335 product)
directly. The soundness callback shape `(d) (m) (frameconds) (w) (h_ctx)` already
exists per system; `FC m` must be destructured into the frame-cond arguments
that `*_soundness` expects. A thin per-system adapter (`fun m hFC => <sys>_soundness …`)
handles the destructuring, keeping the generic theorem FC-agnostic.

**7.2 Parametric `strong_completeness`** (the high-value target — ~50 lines each
collapses to a ~5-line instantiation):

```
theorem strong_completeness {Axioms} {FC} {Γ} {φ}
    (h_implyK …) (h_implyS …) (h_efq …) (h_peirce …)
    (truthLemma : ∀ (S : CanonicalWorld Axioms) (φ : Proposition Atom),
        Satisfies (CanonicalModel Axioms) S φ ↔ φ ∈ S.val)
    (canonical_FC : FC (CanonicalModel Axioms))
    (h : ModalSemanticEntails FC Γ φ) :
    ModalSetDerivable Axioms Γ φ
```

The body is exactly K/Completeness.lean:286–323 with `k_truth_lemma … w`
replaced by `truthLemma w` and `True.intro` replaced by `canonical_FC`.

**7.3 Parametric `strong_completeness_iff`, `compactness`, `weak_completeness`**:
thin wrappers identical to K:330–365, generic over the same parameters.

**7.4 Per-system instantiation** (the refactor target). Each system file becomes,
schematically:

```
def <sys>FC : ∀ {World}, Model World Atom → Prop := fun m => <frame conds>
theorem <sys>_canonical_FC : <sys>FC (CanonicalModel (@<Sys>Axiom Atom)) :=
  ⟨canonical_refl (.implyK)(.implyS)(.modalT), …⟩   -- per system
-- then five one-liners delegating to the parametric cascade with the
-- pre-applied truth lemma:
--   (fun S φ => <family>_truth_lemma (.implyK)…(.modalT?) S φ)
```

T-, K-, D-family systems differ only in which `<family>_truth_lemma` is supplied
and which `canonical_*` callbacks build `<sys>_canonical_FC`.

**7.5 K and D files**: keep their unique truth-lemma infra
(`k_*`/`d_*` definitions); only their *cascade tails* (K:262–367, D:339–467) are
replaced by parametric instantiations.

## 8. Open Decisions for the Planner

1. **FC normalization vs. signature preservation**: Switching T/S4/S5/TB/D-family
   public theorem signatures from inlined `∀`-hypotheses to
   `ModalSemanticEntails FC` changes their *statement form*. Downstream consumers
   (`Metalogic/InterSystem/`, any `ProofSystem/Instances` users) may depend on the
   current shape. **Action for planner**: grep `*_strong_completeness`,
   `*_compactness`, `*_completeness` call sites before changing signatures, or
   provide back-compat wrappers. (Out of scope for read-only research; flagged.)
2. **Soundness leg threading**: decide whether the parametric `strong_soundness`
   takes a soundness *callback* (cleanest, FC-agnostic) vs. re-deriving from
   per-axiom validity. Recommend the callback delegating to the 335 `*_soundness`.
3. **Where `<sys>FC` lives**: as a named `def` per system (lints: needs docstring,
   lowerCamelCase) vs. inline `fun m => …` at each instantiation. Named def reduces
   repetition across the system's five theorems.

## 9. Zero-Debt / Lint Notes

- This is pure plumbing; **no `sorry` risk** — every step reuses an existing,
  already-proven lemma. If any instantiation fails to typecheck it indicates an
  FC-shape mismatch, resolvable by adapter, not by sorry.
- New `def <sys>FC` declarations need docstrings (docBlame), lowerCamelCase names
  (no underscores → use `tFC`/`s5FC` or `Frame`-suffixed camelCase), and live
  inside the `Cslib.Logic.Modal` namespace block (topNamespace).
- Parametric theorems are Prop-valued → use `theorem`, not `def` (defLemma).
- Watch `unusedSectionVars` on the universe `u` / `variable {Atom}` — mirror the
  existing Completeness.lean section discipline.

## 10. Suggested Phase Decomposition (for /plan)

1. **Phase 1**: Add parametric `strong_soundness` + `strong_completeness` to
   `Metalogic/Completeness.lean`; build-verify against K by re-instantiating K.
2. **Phase 2**: Add parametric `strong_completeness_iff`, `compactness`,
   `weak_completeness`; finish K instantiation; `lake build` K.
3. **Phase 3**: Refactor T-family (T, S4, S5, TB) using `truth_lemma`.
4. **Phase 4**: Refactor K-family (B, K4, K5, K45, KB5) using `k_truth_lemma`.
5. **Phase 5**: Refactor D-family (D4, D5, D45, DB) + D cascade tail using
   `d_truth_lemma`.
6. **Phase 6**: Full `lake build` + CI (`checkInitImports`, `lint-style`, `shake`);
   confirm no signature-break in `InterSystem/`.

## References

- Blackburn, de Rijke, Venema — *Modal Logic* (2002), Ch. 4 Thms 4.20–4.28
  (canonical model, existence lemma, truth lemma, completeness).
- Task 335 landed refactor: `Cslib/Logics/Modal/Metalogic/Soundness.lean` +
  `Systems/*/Soundness.lean` (structural template for this cascade).
