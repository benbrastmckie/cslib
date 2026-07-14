# Implementation Plan: CS5 Constructive Completeness via the Symmetric Tail

- **Task**: 509 - rescope_CK_CS5_constructive_completeness
- **Status**: [NOT STARTED]
- **Effort**: 20 hours
- **Dependencies**: None (task 508's CS4 completeness has landed; its CS5 negative verdict is refuted and superseded by this task)
- **Research Inputs**: `specs/509_rescope_CK_CS5_constructive_completeness/reports/01_cs5-symmetric-tail-construction.md`
- **Artifacts**: plans/01_cs5-symmetric-tail-completeness.md (this file)
- **Standards**: plan-format.md, status-markers.md, artifact-management.md, tasks.md, `.claude/rules/artifact-formats.md`, `.claude/rules/plan-format-enforcement.md`, `.claude/rules/cslib.md`, CONTRIBUTING.md, NOTATION.md, ORGANISATION.md
- **Type**: cslib
- **Lean Intent**: false

## Overview

Task 508 published a mechanized negative verdict on CS5 constructive completeness. That verdict is
refuted: its candidate frame condition `cs5FCweak` omitted *plain symmetry* (`r w u → r u w`),
which is exactly the clause `bDia` (`◇□A → A`) needs, and its countermodel relation is itself
non-symmetric. This plan lands the refutation and then pushes CS5 completeness as far as the
mathematics allows.

The route is `cs5FC''` (refl + plain trans + plain symm + the `cs4FC'` re-basing clause +
`FCsym_box`), over which all 17 CS5 axioms are already proved sound with zero axiom dependencies,
plus a canonical model built on the **symmetric tail**
`cs5Tail H = {t | QuasiPrime t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}`. Symmetry of the canonical relation
is then *definitional* rather than derived, so the negation-completeness objection that blocked
tasks 501 and 508 never arises.

Phases 1-3 are transcription of already-verified probe code and retire the false negative currently
published in `CS5.lean`. Phases 4-7 are ordinary canonical-model work reusing the pre-existing
`prime_set_exclusion`. Phases 8-10 attack the single genuinely open sub-problem — the truth lemma's
box-backward case — and Phase 11 assembles. **Definition of done**: `CS5.lean` contains
`cs5_soundness_completeness`, sorry-free and axiom-clean; or, if Phase 10 does not close, `CS5.lean`
contains Phases 1-8's results plus the obstruction stated as a *mechanized theorem* with the
docstring locating it correctly. No `sorry`, no vacuous definition, no placeholder is acceptable in
either outcome.

### Research Integration

From `reports/01_cs5-symmetric-tail-construction.md`:

- **`cs5FC''` and `cs5_axiom_sound''` are verified** (`probes/cs5-symmetry-probe.lean`), all 17
  axioms, `#print axioms` reports no axiom dependencies at all. Phases 1-2 are transcription.
- **`cs5FC → cs5FC''`** (`cs5FC_implies_cs5FC''`), so this is a genuine weakening: validity over
  `cs5FC''` is *stronger*, which is the same direction that made CS4 completeness work.
- **The symmetric tail is forced, not chosen**: `fcbdia_forces_symmetry` shows any `bDia`-adequate
  frame condition implies `boxInv u.head ⊆ w.head` on any segment-based world type. Task 508 read
  this implication as the obstruction; it is the specification.
- **`prime_set_exclusion` already exists** (`Foundations/Logic/Metalogic/PrimeExclusion.lean:558`,
  from task 480): Lindenbaum against an entire *set* `E` with a `DerivExcludes` precondition. Both
  501 and 508 predicted new Lindenbaum machinery was needed; they were looking at the
  single-formula lemma.
- **508 §4(c)'s rejection of simultaneous exclusion does not transfer**: it rejected it because
  `◇(A ∨ B) → ◇A ∨ ◇B` is underivable in CK. True but irrelevant — the exclusion set here is a set
  of *boxes*, and `⊢ (□B ∨ □B') → □(B ∨ B')` **is** derivable (`or_box_imp_box_or`, pure CK).
- **`cs5Tail`'s refl / symm / trans / `Set.univ`-freeness / diamond-backward are verified** at the
  theory level (`probes/cs5-tail-probe.lean`), which also verifies `cs5_boxInv_subset_iff`
  (`boxInv T ⊆ H ↔ T ⊆ diaInv H` over CS5 — the box-inverse and diamond-inverse relations coincide).
  Only the `CS5Segment` wrapper remains.
- **The one open sub-problem** is the truth lemma's box-backward case, and its naive route is
  *mechanically excluded* (`cs5_symmetric_tail_box_gap`) and shown *non-vacuous* (a three-world
  `cs5FC''` countermodel realizes exactly its hypotheses).
- **The open sub-problem is published, as Pacheco's Lemma 18** (`Collapsing Constructive and
  Intuitionistic Modal Logics`, arXiv:2408.16428v2). Pacheco works in exactly our setting
  (`CKB := CK + {B□, B◇}`, fallible worlds, primitive ∀∃ diamond) and his canonical relation
  `∼c` is our `cs5Tail` (the report verifies the identity via `cs5_boxInv_subset_iff`). His Lemma 18
  is the pair-Zorn construction the box-backward case needs. **But the report has already audited
  its primeness step (Lemma 16) and found it unsound**: it argues `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, which is
  negation-completeness — the exact illicit move prime theories do not license. The report quotes the
  broken step directly. The pair-Zorn *skeleton* is portable; the primeness step must be reproved,
  modelled on the in-library `set_maximal_is_prime` (`PrimeExclusion.lean:428`), which does the
  one-sided case correctly.
- **CS5 ≡ IS5, confirmed and design-relevant** (report §4.5.2). Pacheco's Theorem 13 collapses CKB to
  IKB; his Conclusion states DB/TB/KB5/S5 constructive and intuitionistic variants coincide. So CS5
  is theorem-for-theorem Simpson's IS5, unlike CK/CT/CS4 which genuinely differ from their
  intuitionistic counterparts. Corroborated mechanically in our own system: `B` re-derives CK's
  dropped `k5` (508's `cs5_dia_bot_imp_bot`) and `k3` (the new verified `cs5_dia_or`:
  `⊢ ◇(A ∨ B) → ◇A ∨ ◇B`, `probes/cs5-k3-probe.lean`). The completeness theorem is still worth
  having — it targets the fallible-world *segment* semantics, not IS5's birelational one — but
  `CS5.lean` must document the collapse rather than present CS5 as a constructively distinct system.

### Prior Plan Reference

No prior plan exists for task 509. Task 508's plan and probes are treated as **reference and
counter-reference**: its CS4 machinery (`cs4FC'`, `cs4Tail`, `CS4Segment`, the truth lemma shape) is
the structural template Phases 5-7 and 11 mirror, while its CS5 conclusions are refuted and its
`cs5FCweak` route is a recorded dead end (see Risks).

### Roadmap Alignment

No `specs/ROADMAP.md` exists in this repository; no roadmap phases are included.

## Goals & Non-Goals

**Goals**:

- Land `cs5FC''` and CS5 soundness over it (all 17 axioms), sorry-free and axiom-clean.
- Correct `CS5.lean`'s module docstring, which currently publishes task 508's refuted claim that CS5
  completeness is unreachable by the CS4 technique. Correct `SegmentLindenbaum.lean:18`'s
  "two-level tail-assembly fixpoint does not arise" claim, which is true for CK and false for CS5.
- Build the symmetric-tail canonical model (`cs5Tail`, `CS5Segment`, `cs5Mreach`) and prove
  `cs5FC'' cs5Mreach`.
- Resolve the box-backward pair construction, or state the obstruction as a mechanized theorem.
- Land the two new verified library lemmas `cs5_dia_or` (`k3`) and `cs5_boxInv_subset_iff`.
- Document, in `CS5.lean`, that CS5 ≡ IS5 as a theorem set (Pacheco Theorem 13), corroborated by
  `k3`/`k5` both being derivable in CS5 — so the library does not present CS5 as a constructively
  distinct system.
- Add `Pacheco2024` and `ArisakaDasStrassburger2015` to `references.bib` and cite them where used.

**Non-Goals**:

- *Proving* a CKB/IKB-style **collapse** theorem (i.e. mechanizing `CKB ⊢ φ ⟺ IKB ⊢ φ`). The
  collapse is an established fact (Pacheco Theorem 13) that this plan *documents* and corroborates
  via `k3`/`k5`, but does not re-prove — our target is completeness for the fallible-world segment
  semantics, a different semantics from IS5's birelational one. If a phase's construction would
  additionally establish a collapse as a byproduct, that must be surfaced explicitly (see Phase 9),
  not landed silently.
- Re-deriving canonical symmetry from maximality. Symmetry is definitional here; this is the whole
  point of the design.
- Touching `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, `CKTruthLemma.lean`. Task 501/508
  assets are preserved unchanged.
- Any `sorry`, any `def X := True`-style vacuous placeholder, or any new axiom.
- Reviving `cs5FCweak`, `cs5_dia_bot_imp_bot`-based tail redesign, sequential Lindenbaum for the
  box-backward case, or `box(A ∨ □D) → □A ∨ D` (all recorded dead ends — see Risks).

## Risks & Mitigations

| Risk | Impact | Likelihood | Mitigation |
|------|--------|------------|------------|
| Box-backward pair construction (Phases 9-10) does not close | H | M | Phases 1-8 are a self-contained, independently valuable increment landed first. Fallback is mandatory and specified: state the obstruction as a mechanized theorem (Phase 11 fallback), never a `sorry`. |
| Pacheco Lemma 16 (primeness-from-maximality, reused by his Lemma 18) is **confirmed unsound** — the research report quotes it arguing via `φ ∉ Θ ⟹ ¬φ ∈ Θ`, i.e. negation-completeness | H | H (certain) | Do **not** transcribe Lemma 18's primeness step. Phase 8 confirms the verdict against the paper and *builds the repair* — primeness from pair-poset maximality, modelled on the in-library `set_maximal_is_prime` (`PrimeExclusion.lean:428`), which does the one-sided case correctly. Phase 9-10 consume the repaired lemma. |
| The repaired primeness argument does not go through for the *two-sided* pair poset even though it works one-sided | H | M | Phase 8 delivers the repair as a standalone probe lemma before the pair poset is built, so the risk is isolated and surfaces early. If it fails, escalate to Phase 11 Branch B (mechanized obstruction). |
| Re-entering a recorded dead end | M | M | Dead ends are enumerated in Non-Goals and repeated in the phases that could plausibly drift into them. `cs5_symmetric_tail_box_gap` and the three-world countermodel are mechanized guards. |
| Porting Pacheco on faith, importing his collapse (`W⊥ = ∅`) into a fallible-worlds setting | M | M | Phase 9 requires an explicit check that the pair poset does not force `Set.univ` into either component, and requires flagging any collapse consequence rather than landing it silently. |
| Item 5's list-splitting/finite-conjunction bookkeeping is larger than "low-med" | M | L | Phase 4 is scoped independently, in its own file, with no dependency on the CS5 phases; it can be sized and landed on its own. `prime_set_exclusion`'s `hCut` parameter already accepts the singleton form, so the generalization is confined to splitting a context drawn from a *union of two sets*. |
| CI gate failures (shake/lint-style/checkInitImports) accumulate to the end | L | M | Every phase runs the full CI pipeline as its verification step; nothing lands red. |
| `CS5.lean` grows past a reviewable size (currently 261 lines; this plan roughly triples it) | L | M | If `CS5.lean` exceeds ~700 lines after Phase 7, split the canonical-model half into `CS5Canonical.lean` and re-run `lake exe mk_all --module`. Decide at Phase 7's verification step, not earlier. |

## Implementation Phases

**Dependency Analysis**:

| Wave | Phases | Blocked by |
|------|--------|------------|
| 1 | 1, 4 | -- |
| 2 | 2 | 1 |
| 3 | 3 | 2 |
| 4 | 5 | 3 |
| 5 | 6 | 4, 5 |
| 6 | 7 | 6 |
| 7 | 8 | 7 |
| 8 | 9 | 8 |
| 9 | 10 | 9 |
| 10 | 11 | 10 |

Phases within the same wave can execute in parallel. Only Wave 1 has genuine parallelism: Phase 1
owns `CKExtension.lean` + `references.bib`, Phase 4 owns `SegmentLindenbaum.lean`, and their
territories are disjoint. Phases 2, 3, 5, 6, 7 all write `CS5.lean` and are serialized for that
reason even where their mathematical dependencies are weaker.

**Sequencing rationale**: Phases 1-3 are transcription of verified probe code and are ordered first
so the task banks a sorry-free, independently valuable increment — the refutation of 508's published
negative result — before any research risk is taken. Phases 8-10 are the research-risk group and are
deliberately last.

---

### Phase 1: `cs5FC''` frame condition and bibliography [NOT STARTED]

**Goal**: Land the weakened CS5 frame condition beside `cs4FC'`, prove it is a genuine weakening,
and add the two literature entries the later phases cite.

**Tasks**:

- [ ] Add `cs5FC''` to `CKExtension.lean` beside `cs5FC` (which stays), transcribed from
      `probes/cs5-symmetry-probe.lean`:
      refl `∀ w, r w w` (tBox, tDia); plain trans `∀ {w u t}, r w u → r u t → r w t` (fourDia);
      plain symm `∀ {w u}, r w u → r u w` (bDia); the `cs4FC'` re-basing clause
      `∀ {w u u' t}, r w u → u ≤ u' → r u' t → ∃ v, w ≤ v ∧ r v t` (fourBox); and
      `FCsym_box : ∀ {w u u'}, r w u → u ≤ u' → ∃ t, r u' t ∧ w ≤ t` (bBox).
- [ ] Add `cs5FC_implies_cs5FC''`, mirroring the existing `cs4FC_implies_cs4FC'` in shape.
- [ ] Docstring `cs5FC''`: state per-clause which axiom each clause validates, and state plainly
      that `cs5FCweak` (task 508) is `cs5FC''` minus plain symmetry and minus plain transitivity,
      which is why `bDia` failed over it.
- [ ] Add `Pacheco2024` to `references.bib`: Pacheco, "Collapsing Constructive and Intuitionistic
      Modal Logics", arXiv:2408.16428, 2024. Confirm exact author list, title, and venue against the
      literature corpus before writing the entry — do not transcribe from this plan.
- [ ] Add `ArisakaDasStrassburger2015` to `references.bib`: Arisaka, Das, Straßburger, "On Nested
      Sequents for Constructive Modal Logics", Logical Methods in Computer Science 11(3:7), 2015,
      pp. 1-33. Confirm details against the corpus.

**Timing**: 1 hour

**Depends on**: none

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — add `cs5FC''`,
  `cs5FC_implies_cs5FC''`. Do not modify `cs5FC`, `cs4FC`, `cs4FC'`, `ctFC`, or
  `ckvalidFC_completeness`.
- `references.bib` — two new entries.

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CKExtension` succeeds.
- Full CI gate: `lake build`, `lake exe checkInitImports`, `lake exe lint-style`, `lake lint`,
  `lake test`, `lake shake --add-public --keep-implied --keep-prefix`.
- `#print axioms cs5FC_implies_cs5FC''` reports no axiom dependencies.
- Confirm the two BibTeX keys resolve: grep `references.bib` for both keys.

**Reference**: `probes/cs5-symmetry-probe.lean` (verified, compiles, axiom-free).

---

### Phase 2: CS5 soundness over `cs5FC''` and the two derivability lemmas [NOT STARTED]

**Goal**: Prove all 17 CS5 axioms sound over `cs5FC''`, and land the disjunction-of-boxes identity
that makes the later `prime_set_exclusion` side conditions dischargeable. This is the half task 508
declared impossible.

**Tasks**:

The six declarations here are `cs5_axiom_sound''`, `cs5_soundness''`, `cs5_soundness_derivable''`,
`or_box_imp_box_or`, `dia_or_box_imp_or`, plus the two new library lemmas `cs5_dia_or` and
`cs5_boxInv_subset_iff` (eight total).

- [ ] Add `cs5_axiom_sound''` to `CS5.lean`, transcribed from `probes/cs5-symmetry-probe.lean`. It
      is `cs5_axiom_sound`'s proof (CS5.lean:158) with exactly four cases changed:
      `fourDia` uses plain transitivity `htrans hru hut`; `fourBox` uses `hfour hru hu' hrt` and
      discharges `□A` at the re-based `v` (the CS4 trick); `bDia` uses plain symmetry `hsymm hru`;
      `bBox` uses `hsymbox hru hu'` and gets `A@t` by persistence from `A@w'`. The other 13 cases are
      verbatim.
- [ ] Add `cs5_soundness''` and `cs5_soundness_derivable''` — mechanical re-threads of
      `cs5_soundness` (CS5.lean:221) and `cs5_soundness_derivable` (CS5.lean:254).
- [ ] Retain the existing `cs5_axiom_sound` / `cs5_soundness` / `cs5_soundness_derivable` over
      `cs5FC`; re-derive them as corollaries via `cs5FC_implies_cs5FC''` if that shortens the file,
      otherwise leave them untouched. Do not delete them.
- [ ] Add `or_box_imp_box_or` (`⊢ (□B ∨ □B') → □(B ∨ B')`, pure CK: necessitation + `Kb` + `orI`/
      `orE`) and `dia_or_box_imp_or` (`⊢ ◇(□B ∨ □B') → (B ∨ B')`, via `Kd` + `bDia`), transcribed
      from `probes/cs5-canonical-probe.lean` along with their private helpers
      `box_mono_or_left` / `box_mono_or_right`.
- [ ] Docstring `or_box_imp_box_or` with the point that makes it load-bearing: the exclusion set in
      this construction is a set of **boxes**, not of diamonds, and boxes distribute the right way —
      which is precisely why task 508 §4(c)'s rejection of simultaneous exclusion does not apply.
- [ ] Add `cs5_dia_or` (`⊢ ◇(A ∨ B) → ◇A ∨ ◇B`, the `k3` axiom bare CK lacks), transcribed from
      `probes/cs5-k3-probe.lean` (verified). This is independently interesting and is one of the two
      derivations (`k3` here, `k5` = 508's `cs5_dia_bot_imp_bot`) that corroborate the CS5 ≡ IS5
      collapse Phase 3 documents. It also voids 508 §4(c) a second time (its premise, `◇(A∨B) → ◇A∨◇B`
      underivable, is false for CS5).
- [ ] Add `cs5_boxInv_subset_iff` (`boxInv T ⊆ H ↔ T ⊆ diaInv H` for quasi-prime `H`, `T`; `→` is
      `bBox`, `←` is `bDia`), transcribed from `probes/cs5-tail-probe.lean` (verified). `diaInv`
      already exists (`Segment.lean:106`). This lemma establishes that the box-inverse tail clause
      and Pacheco's diamond-inverse `∼c` relation are the *same* relation — used in Phase 3's
      docstring and available to Phase 9 if the pair poset is more natural in diamond-inverse form.

**Timing**: 2 hours

**Depends on**: 1

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — add the eight declarations above. Do not
  touch the module docstring in this phase (Phase 3 owns it).

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5` succeeds.
- Full CI gate (as Phase 1).
- `#print axioms cs5_axiom_sound''` reports **no axiom dependencies at all** — this is the probe's
  measured result and is a hard gate, not an aspiration. Same check for `or_box_imp_box_or`,
  `dia_or_box_imp_or`, `cs5_dia_or`, and `cs5_boxInv_subset_iff`.
- `grep -c sorry` on `CS5.lean` returns 0.

**Reference**: `probes/cs5-symmetry-probe.lean`, `probes/cs5-canonical-probe.lean`,
`probes/cs5-k3-probe.lean`, `probes/cs5-tail-probe.lean` (all verified).

---

### Phase 3: Correct the `CS5.lean` and `SegmentLindenbaum.lean` docstrings [NOT STARTED]

**Goal**: Retire the false negative result currently published in the library. This phase is the
deliverable that makes Phases 1-2 matter to a reader.

**Tasks**:

- [ ] Rewrite `CS5.lean:30-60`. Specifically:
      - `CS5.lean:34-41` asserts `bDia` is "not sound over `cs5FCweak`, the natural CS5 analogue of
        the weakened frame condition that makes CS4 work" and that this is "a soundness failure
        which no amount of canonical-model work on the completeness side can fix". Replace: state
        that `cs5FCweak` is **not** the natural analogue — it omits plain symmetry (the clause
        `bDia` needs) and plain transitivity — that its countermodel relation is itself
        non-symmetric (`wr'_not_symm`), and that `cs5_axiom_sound''` proves all 17 axioms sound over
        `cs5FC''`. Keep 508's countermodel correctly attributed: it is *sound*, it simply does not
        bear on `cs5FC''`.
      - `CS5.lean:43-47` (`FCbdia` fails canonically at `u := cexpl`) holds only for `ofHead`'s
        maximal tail. Replace: under `cs5Tail`, `boxInv Set.univ = Set.univ`, so no consistent head
        has an exploding tail member.
      - `CS5.lean:48-54` nominates `cs5_dia_bot_imp_bot` as "one lead" and calls canonical symmetry
        "the known-hard core ... whose classical proof needs negation-completeness". Replace both:
        `Set.univ`-freeness follows directly from the tail's `boxInv t ⊆ H` clause, and canonical
        symmetry is obtained **by construction**, never derived, so the negation-completeness
        objection never arises.
      - State the *actual* open problem: the truth lemma's box-backward case, with a forward
        reference to `cs5_symmetric_tail_box_gap` (landed in Phase 5 or 8) as the mechanized reason
        the sequential route fails.
- [ ] **Document the CS5 ≡ IS5 collapse** (report §4.5.2; item 11). Add a docstring paragraph
      stating that CS5 is theorem-for-theorem Simpson's IS5 (Pacheco `Pacheco2024` Theorem 13; his
      Conclusion notes DB/TB/KB5/S5 constructive and intuitionistic variants coincide), unlike
      CK/CT/CS4 which genuinely differ from their intuitionistic counterparts. Corroborate in-system:
      `B` re-derives CK's dropped `k3` (`cs5_dia_or`, Phase 2) and `k5` (508's
      `cs5_dia_bot_imp_bot`) — cite `ArisakaDasStrassburger2015` for the `B ⊢ k3, k5` fact. State
      *why the completeness theorem is still worth having*: it targets the fallible-world segment
      semantics, not IS5's birelational one. This is a required deliverable, not an optional note —
      the library must not present CS5 as a constructively distinct system.
- [ ] Add a docstring note (or cite Pacheco's own diagnostic) that prime-theory canonical
      completeness works for CS5 *precisely because* `B` collapses it out of the fallible-world
      regime, and is therefore **not** a template for other CK extensions. CS4's `excl` field exists
      because CS4 does not collapse.
- [ ] Correct `SegmentLindenbaum.lean:18` ("The plan's feared 'two-level tail-assembly fixpoint'
      does not arise"). It is true for CK/CT/CS4 and **false for CS5**. Scope the sentence to the
      logics it holds for and note the CS5 exception.
- [ ] Update `CS5.lean`'s `## Main Definitions` and `## References` sections: add `cs5FC''`,
      `cs5_axiom_sound''`/`cs5_soundness''`/`cs5_soundness_derivable''`, `or_box_imp_box_or`,
      `dia_or_box_imp_or`; add the `Pacheco2024` and `ArisakaDasStrassburger2015` BibKeys if cited
      in the prose.
- [ ] Point the "for the full mechanized analysis" pointer at task 509's report and probes rather
      than 508's.

**Timing**: 45 minutes

**Depends on**: 2

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — module docstring only.
- `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` — module docstring only.

**Verification**:

- Full CI gate (as Phase 1). `lake exe lint-style` is the operative check for docstring line length.
- `grep -n "cs5FCweak" CS5.lean` returns only occurrences that correctly describe it as *not* the
  natural analogue; no surviving sentence claims CS5 completeness is unreachable by canonical-model
  work.
- Every BibKey cited in the new prose resolves in `references.bib`.

**Note**: this docstring states the *current* honest status. Phase 11 revises it to final status.

---

### Phase 4: List-splitting and finite-conjunction helpers [NOT STARTED]

**Goal**: Generalize the context-splitting machinery from a singleton to a union of two sets, so the
`DerivExcludes` obligations in Phases 6-7 can be discharged. This is bookkeeping, not mathematics.

**Tasks**:

- [ ] Establish the exact gap first. `prime_set_exclusion`'s `hCut` parameter
      (`PrimeExclusion.lean:558`) already takes the singleton form
      (`(∀ x ∈ L, x ∈ insert a U) → D.Deriv L b → ∃ L', (∀ x ∈ L', x ∈ U) ∧ D.Deriv L' (a → b)`), which
      `modal_deriv_imp_of_union` (`Intuitionistic/PrimeTheory.lean:173`) supplies. The gap is
      elsewhere: Phases 6-7 instantiate `S` at a **union of two sets** (`boxInv u'.head ∪ w.head`,
      `w.head ∪ boxInv t.head`), and discharging `DerivExcludes` there needs a derivation context
      `L ⊆ X ∪ Y` split into `L₁ ⊆ X`, `L₂ ⊆ Y` with the `L₂` part discharged as a finite
      conjunction `⋀L₂`. Confirm this reading against the two call sites before writing code; if
      `hCut` alone suffices, say so and cut this phase to its verification step.
- [ ] Add a list-splitting lemma: `L ⊆ X ∪ Y → ∃ L₁ L₂, L₁ ⊆ X ∧ L₂ ⊆ Y ∧ (permutation/derivability
      relation between L and L₁ ++ L₂)`. Match the existing style of `bigOr_append_left` /
      `bigOr_append_right` (`PrimeExclusion.lean:359`, `:372`), which are the closest precedent.
- [ ] Add a finite-conjunction former `bigAnd` (or reuse one if `lean_local_search` finds it —
      check before defining) plus the discharge lemma `D.Deriv (L₁ ++ L₂) b → D.Deriv L₁ (⋀L₂ → b)`.
- [ ] Reuse-first: run `lean_local_search` and `lean_loogle` for existing `bigAnd`/conjunction-
      folding machinery in CSLib and Mathlib before adding anything new. Record what was searched
      and what was found in the phase's summary.

**Timing**: 2 hours

**Depends on**: none

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` — new helpers. (If the helpers
  turn out to be logic-generic rather than modal-specific, `Foundations/Logic/Metalogic/PrimeExclusion.lean`
  is the better home; decide by whether the statement mentions `Proposition`/`box`.)

**Territory note**: this phase runs in Wave 1 in parallel with Phase 1. It must not touch
`CKExtension.lean`, `CS5.lean`, or `references.bib`. Phase 3 also edits `SegmentLindenbaum.lean` but
only its module docstring, and Phase 3 is in Wave 3 — no conflict.

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.SegmentLindenbaum` succeeds.
- Full CI gate (as Phase 1).
- `#print axioms` on each new helper; record the result. Classical dependencies are acceptable here
  if genuinely needed, but must be reported, not absorbed silently.
- No existing declaration in `SegmentLindenbaum.lean` changes signature.

---

### Phase 5: The symmetric tail and `CS5Segment` [NOT STARTED]

**Goal**: Land `cs5Tail`, the `CS5Segment` world type, and the five canonical facts already verified
at theory level — including the definitional symmetry that is the heart of this design.

**Tasks**:

- [ ] Add closure helpers `cs5_box_four` (`□B ∈ H → □□B ∈ H`, axiom `4`) and `cs5_boxInv_subset`
      (`boxInv H ⊆ H`, axiom `T`), transcribed from `probes/cs5-tail-probe.lean`.
- [ ] Add `cs5Tail H := {t | QuasiPrime CS5ModalAxiom t ∧ boxInv H ⊆ t ∧ boxInv t ⊆ H}`. Docstring
      it with `fcbdia_forces_symmetry`'s content: the `boxInv t ⊆ H` clause is **not** a design
      choice — every `bDia`-adequate frame condition forces it on any segment-based world type.
      Note that CS5 needs **no** `E`/exclusion parameter, unlike `cs4Tail`.
- [ ] Add `cs5Seg`, `structure CS5Segment`, `instance : Preorder (CS5Segment Atom)` via
      `Preorder.lift`, `cs5Mreach`, `CS5Segment.ofHead`, `cs5Val`, `cs5Bot`, mirroring
      `CS4.lean:341-455`. CS5 has no `CS4Segment.diaRefuting` analogue and needs none.
- [ ] Transcribe the five verified facts from `probes/cs5-tail-probe.lean`: `cs5Tail_refl`,
      `cs5Tail_symm` (`⟨hH, h.2.2, h.2.1⟩` — the two clauses simply swap), `cs5Tail_trans` (uses
      `cs5_box_four` on each side), `cs5Tail_univ_free`, `cs5Tail_dia_of_mem`. (`cs5_boxInv_subset_iff`
      is landed in Phase 2; if the `cs5_box_four`/`cs5_boxInv_subset` closure helpers were already
      added there, reuse them rather than duplicating.)
- [ ] Transcribe `fcbdia_forces_symmetry` and `cs5_symmetric_tail_box_gap` from
      `probes/cs5-canonical-probe.lean`. These are load-bearing *documentation of the design's
      constraints* and are cited by Phase 3's docstring; land them as real theorems.
- [ ] Add the upward-closure lemmas `cs5Val_upward_closed`, `cs5Bot_upward_closed`, `cs5Bot_val`,
      `cs5Bot_mreach`, `cs5Bot_mreach_wit`, mirroring `CS4.lean:526-550`.

**Timing**: 1.5 hours

**Depends on**: 3

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5` succeeds.
- Full CI gate (as Phase 1).
- `#print axioms cs5Tail_symm` reports **no axiom dependencies at all** (the probe's measured
  result). Also check `cs5Tail_refl`, `cs5Tail_trans`, `cs5Tail_univ_free`, `cs5Tail_dia_of_mem`,
  `cs5_symmetric_tail_box_gap`.
- `grep -c sorry` returns 0.
- `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, `CKTruthLemma.lean` are unmodified
  (`git diff --stat` confirms).

---

### Phase 6: `diam_witness` via `prime_set_exclusion` [NOT STARTED]

**Goal**: Prove the diamond witness for the symmetric tail — the first of three obligations that go
through `prime_set_exclusion`, and the one that establishes the four-step discharge pattern the
other two reuse.

**Tasks**:

- [ ] Prove `cs5_diam_witness`: `◇A ∈ H` ⟹ `∃ t ∈ cs5Tail H, A ∈ t`. Instantiate
      `prime_set_exclusion` at `S := boxInv H ∪ {A}` and `E := {□B | B ∉ H}`.
- [ ] Discharge `DerivExcludes` by the report's four-step argument:
      (1) suppose `S ⊢ bigOr l` for `l` drawn from `E`; set `D := ⋁Bᵢ`; each `Bᵢ ∉ H`, so `D ∉ H` by
      primality of `H`;
      (2) `or_box_imp_box_or` gives `⊢ ⋁□Bᵢ → □D`, so `S ⊢ □D`;
      (3) `box_mem_of_boxed_context` (`SegmentLindenbaum.lean:100`) + `Kd` place `◇□D` in `H` — for
      this obligation step 3 is direct: `□(A → □D) ∈ H`, then `Kd` on `◇A ∈ H`;
      (4) `bDia` (via `dia_or_box_imp_or`) gives `D ∈ H` — contradiction.
- [ ] Verify the resulting `t` satisfies **both** tail clauses. `boxInv H ⊆ t` is immediate from
      `S ⊆ t`. `boxInv t ⊆ H` is exactly what `DerivExcludes ... E t` buys: `t ∩ E = ∅` means no
      `□B` with `B ∉ H` lies in `t`, i.e. `□B ∈ t → B ∈ H`. Confirm this step explicitly — it is
      where the *set*-valued exclusion earns its keep over the single-formula lemma.
- [ ] Supply `prime_set_exclusion`'s remaining parameters (`hOrI1`, `hOrI2`, `hOrE`, `hEFQ`, `cl`,
      `cl_subset`, `cl_mem_imp`, `cl_admissible_of_cons`, `bot_mem_cl_of_not_cons`, `hCut`,
      `hConsChain`) from the CS5 axiom constructors and `modalDeductiveClosure`. Factor this
      instantiation into a private helper — Phase 7 reuses it twice.

**Timing**: 2 hours

**Depends on**: 4, 5

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean`

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5` succeeds.
- Full CI gate (as Phase 1).
- `#print axioms cs5_diam_witness` — Zorn is used via `prime_set_exclusion`, so
  `Classical.choice`/`propext`/`Quot.sound` are expected here. Record the exact set; anything beyond
  those three is a defect.
- `grep -c sorry` returns 0.

---

### Phase 7: Canonical `FCsym_box` and `FC4'`; `cs5FC'' cs5Mreach` [NOT STARTED]

**Goal**: Discharge the two remaining frame clauses canonically and assemble the full statement that
the canonical relation satisfies `cs5FC''`.

**Tasks**:

- [ ] Prove canonical `FCsym_box` (`bBox`'s clause). Instantiate `prime_set_exclusion` at
      `S := boxInv u'.head ∪ w.head`, exclusion at `X := u'.head`. Step 3 of the four-step discharge
      needs `◇C ∈ u'.head` for `C := ⋀Δ ∈ w.head`: `bBox` gives `□◇C ∈ w.head`, so
      `◇C ∈ boxInv w.head ⊆ u.head ⊆ u'.head`. (This is task 508 §5.1's paper sketch, which is
      correct; it is the finite-conjunction `⋀Δ` here that consumes Phase 4's helpers.)
- [ ] Prove canonical `FC4'` (`fourBox`'s re-basing clause). Instantiate at
      `S := w.head ∪ boxInv t.head`, exclusion at `X := t.head`. Step 3 needs `◇C ∈ t.head`: `bBox`
      gives `□◇C ∈ w.head`, then `4` gives `□□◇C ∈ w.head`, so
      `□◇C ∈ boxInv w.head ⊆ u.head ⊆ u'.head`, so `◇C ∈ boxInv u'.head ⊆ t.head`.
- [ ] Assemble `cs5FC''_cs5Mreach : cs5FC'' (@cs5Mreach Atom)`, mirroring `cs4FC'_cs4Mreach`
      (`CS4.lean:441`). Its five components are: `cs5Tail_refl` (Phase 5), `cs5Tail_trans`
      (Phase 5), `cs5Tail_symm` (Phase 5), `FC4'` (this phase), `FCsym_box` (this phase).
- [ ] File-size decision point: if `CS5.lean` now exceeds ~700 lines, split the canonical-model half
      into `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean`, run
      `lake exe mk_all --module`, and re-run the full CI gate. Otherwise leave as-is and record the
      line count.

**Timing**: 2 hours

**Depends on**: 6

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (possibly plus a new `CS5Canonical.lean` and
  `Cslib.lean` if the split is taken).

**Verification**:

- `lake build Cslib.Logics.Modal.Metalogic.Constructive.CS5` succeeds.
- Full CI gate (as Phase 1), including `lake exe mk_all --module` if a new file was added.
- `#print axioms cs5FC''_cs5Mreach` — record the axiom set; expect the Zorn three.
- `grep -c sorry` returns 0.

**Milestone**: at the end of this phase, everything except the box-backward case is done. Commit
before proceeding — Phases 8-10 are the research risk, and this is the last guaranteed-green point.

---

### Phase 8: Repaired primeness-from-pair-maximality lemma [NOT STARTED]

**Goal**: Build the constructive, sorry-free primeness lemma that Pacheco's Lemma 18 needs and his
Lemma 16 supplies unsoundly. The audit verdict is already established (see Background); this phase
does the *repair*, isolated as a standalone probe lemma before the pair poset (Phase 9) consumes it.

**Background** (already established by the research report §4.5.4 — **not** to be re-derived, only
confirmed against the paper): Pacheco 2024 works in exactly our setting — `CKB := CK + {B□, B◇}`
(our `bBox`/`bDia`), fallible worlds, primitive ∀∃ diamond. His Lemma 18 is the two-sided
Lindenbaum pair construction the box-backward case needs: pairs `⟨X, Y⟩` with cross-conditions
`Y□ ⊆ X`, `Y ⊆ X♦`, `ϕ ∉ X ∪ Y`, `⊥ ∉ X ∪ Y` carried as poset invariants, ordered componentwise,
Zorn-maximal. **His primeness step (Lemma 16) is unsound**: the report quotes it deriving primeness
from `ϕ ∉ Θ ⟹ ¬ϕ ∈ Θ`, which is negation-completeness — the exact move prime theories do not
license, and which a Zorn-maximal-in-poset `Θ` does not supply. The report also notes Lemma 16's
statement is garbled (`Υ` written for `Θ`). Do **not** transcribe it. The correct argument derives
the contradiction from *poset-invariant violations*: from `≤`-maximality, adding `ϕ` to the
component must violate some invariant and adding `ψ` must violate some invariant; conclude from
those two failures. CSLib's `set_maximal_is_prime` (`PrimeExclusion.lean:428`) does exactly this for
the one-sided case and is the model for the repair.

**Tasks**:

- [ ] Confirm (do not re-derive) the verdict against the paper: read chunk `ec3a8bddd907f0c4`
      (Lemma 16) and `39fb2b22fa8afe5a` (Lemma 18) via
      `bash .claude/scripts/literature-search.sh --read <chunk_id>`. One read to confirm the report's
      quotation is faithful; if it is not, that is a finding — report it. This is a check, not a
      fresh investigation.
- [ ] Study `set_maximal_is_prime` (`PrimeExclusion.lean:428`) and how `prime_set_exclusion` consumes
      it. Determine whether it already delivers primeness for the *component* theories of a maximal
      pair — i.e. whether the two-sided construction can reuse the one-sided primeness lemma directly
      by projecting the pair order onto one component while holding the other fixed. If so, the
      "repair" is a reuse and this phase is short; record that finding.
- [ ] State and prove the repaired primeness lemma as a standalone probe at
      `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean`:
      from maximality of `⟨X, Y⟩` in the pair poset (Phase 9's poset, stubbed here with its
      invariants as hypotheses), `ϕ ∨ ψ ∈ X ⟹ ϕ ∈ X ∨ ψ ∈ X` (and the same for `Y`), by the
      invariant-violation argument, **not** negation-completeness. Sorry-free.
- [ ] If the invariant-violation argument does **not** close for the two-sided poset (e.g. the
      cross-conditions make the "adding ϕ violates an invariant" step fail): record precisely where,
      and escalate — this is the Phase 11 Branch B trigger surfacing early, which is far better than
      discovering it at Phase 10.

**Timing**: 2 hours

**Depends on**: 7

**Files to modify**:

- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean` (new, probe
  only — nothing lands in `Cslib/` in this phase).

**Verification**:

- `lake env lean specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean`
  exits 0 with no `sorry`.
- `#print axioms` on the repaired lemma — the argument must not smuggle in negation-completeness;
  it should depend on nothing beyond the Zorn three (`Classical.choice`/`propext`/`Quot.sound`) and
  the invariant hypotheses. A dependency on an EM/`Classical.em`-flavoured lemma about `¬ϕ` is a
  red flag to investigate, not accept.
- The probe's docstring states, in one line, whether the repair was a reuse of `set_maximal_is_prime`
  or a fresh argument, and cites `Pacheco2024` Lemma 18 as the (holed) source.

**Gate**: Phase 9 builds the poset whose maximality this lemma consumes; Phase 10 applies this lemma.
Do **not** transcribe Pacheco's primeness step on faith at any later phase.

---

### Phase 9: The pair poset and its Zorn scaffold [NOT STARTED]

**Goal**: Build the simultaneous-pair Zorn scaffold for the box-backward case: the poset, its
invariants, and the chain-upper-bound step. This phase does not yet use maximality.

**Why a pair is required** (established, mechanized, not to be re-litigated): the truth lemma's
box-backward case needs, from prime `H` with `□A ∉ H`, a prime `H' ⊇ H` with `□A ∉ H'` and a prime
`T` with `boxInv H' ⊆ T`, `boxInv T ⊆ H'`, `A ∉ T`. Sequential Lindenbaum provably fails
(`cs5_symmetric_tail_box_gap`: if `□(p ∨ □q) ∈ H` and `q ∉ H` then **every** symmetric-tail member
of `H` contains `p`), and the gap is non-vacuous — the three-world `cs5FC''` countermodel in
`probes/cs5-boxgap-countermodel.lean` realizes exactly those hypotheses at `w`. Enlarging `H'` also
enlarges `boxInv H'`, so the two sides must grow together.

**Tasks**:

- [ ] Define the pair poset: pairs `(X, Y)` of theories ordered componentwise by `⊆`, carrying as
      invariants the cross-conditions (`boxInv X ⊆ Y`, `boxInv Y ⊆ X`) together with the exclusion
      conditions (`□A ∉ X`, `A ∉ Y`) and admissibility of both components. Model the shape on
      `SetExcludingSupersets` (`PrimeExclusion.lean:334`), which is the library's existing
      single-sided analogue.
- [ ] Prove the chain-upper-bound step: the componentwise union of a chain stays in the poset. The
      cross-conditions are the interesting part — `boxInv (⋃ Xᵢ) ⊆ ⋃ Yᵢ` needs `boxInv` to commute
      with directed unions, which holds because `boxInv` is defined pointwise. Model on
      `set_excluding_chain_union`.
- [ ] Prove the base point is in the poset: `(H, T₀)` for a suitable `T₀`. This is where the
      exclusion invariants must be shown consistent at the start; expect to need
      `box_refuting_theory`-style reasoning (`SegmentLindenbaum.lean:168`) plus Phase 4's helpers.
- [ ] Apply `zorn_subset_nonempty` (or the appropriate Mathlib Zorn variant for a product order —
      check `lean_loogle` for the right form; `zorn_subset_nonempty` is what `prime_set_exclusion`
      uses) to obtain a maximal pair. Stop here; maximality is consumed in Phase 10.
- [ ] **Collapse check** (mandatory, per Non-Goals): verify that the poset does not force `Set.univ`
      into either component. Pacheco's Theorem 13 is a *collapse* (CKB ⊢ φ ⟺ IKB ⊢ φ) with canonical
      `W⊥ = ∅`; our route via `cs5FC''` + the symmetric tail is not his and need not inherit it. If
      the construction as built would establish a collapse of CS5 to its intuitionistic counterpart,
      **say so explicitly** in the phase summary and in the handoff — that is a design-relevant fact
      about the CK column that must surface, not be landed silently.

**Timing**: 2 hours

**Depends on**: 8

**Files to modify**:

- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-construction.lean` (new probe
  — prove it out here before landing in `Cslib/`).

**Verification**:

- `lake env lean specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-construction.lean`
  exits 0 with no `sorry`.
- The chain-upper-bound lemma and the base-point lemma are each proved outright, not admitted.
- `#print axioms` on each; expect the Zorn three.
- The collapse check is answered in writing, either way.

**Research risk**: this is the first of two research-risk phases. If the poset cannot be shown
non-empty at the base point, that is itself a finding — escalate to the Phase 11 fallback rather
than weakening the invariants until the statement becomes vacuous.

---

### Phase 10: Maximality to `cs5_box_backward` [NOT STARTED]

**Goal**: The crux. Extract from the maximal pair the two saturation properties the box-backward
case needs, and prove `cs5_box_backward`.

**Tasks**:

- [ ] From the maximal pair `(H', T)`, derive primeness of each component by applying Phase 8's
      repaired primeness lemma (`cs5-pair-primeness.lean`) to each component of the maximal pair.
      This is the step whose Pacheco original (Lemma 16) was unsound; Phase 8 supplies the sound
      replacement. Do not re-derive it here and do not fall back to the negation-completeness route.
- [ ] Derive the saturation condition the countermodel identified as necessary:
      `∀ D, □(A ∨ □D) ∈ H' → D ∈ H'`. This is the property that `H = Th(w)` lacks and
      `H' = Th(w')` has in the three-world countermodel, and it is what makes `T` findable.
- [ ] Prove `cs5_box_backward`: `□A ∉ s.head` ⟹ `∃ s' ≥ s, ∃ Q, cs5Mreach s' Q ∧ A ∉ Q.head`.
- [ ] Cross-check the result against the mechanized guards before believing it: it must be
      consistent with `cs5_symmetric_tail_box_gap` (which forbids a witness at `H` itself when
      `□(p ∨ □q) ∈ H`, `q ∉ H`) and it must produce `H' ∋ q` on the three-world countermodel's
      configuration. If a proof appears that would give a witness at `H` itself, it is wrong —
      `cs5_symmetric_tail_box_gap` is a three-line structural theorem using no CS5 axiom.
- [ ] Do not re-enter: sequential Lindenbaum (`H'` first, then `T`); proving
      `□(A ∨ □D) → □A ∨ D` (mechanically refuted over `cs5FC''` by
      `probes/cs5-boxgap-countermodel.lean`).

**Timing**: 2 hours (hard bound — if not closed, escalate to the Phase 11 fallback rather than
extending)

**Depends on**: 9

**Files to modify**:

- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-construction.lean` (extend).

**Verification**:

- Probe exits 0, no `sorry`, `#print axioms` recorded.
- `cs5_box_backward` is stated at the exact shape Phase 11's truth lemma consumes.
- The two cross-checks above are performed and reported.

**Research risk**: this is the crux and the single highest-risk phase in the plan. Its failure is an
anticipated outcome with a specified fallback (Phase 11), not a blocker.

---

### Phase 11: Assembly, or mechanized obstruction [NOT STARTED]

**Goal**: Close CS5 completeness, or state the obstruction as a theorem. Exactly one of the two
branches executes, decided by Phase 10's outcome.

**Branch A — Phase 10 closed** (`cs5_box_backward` proved):

- [ ] Land Phases 9-10's probe content into `CS5.lean` (or `CS5Canonical.lean` if Phase 7 split).
- [ ] Prove `cs5_truth_lemma (s : CS5Segment Atom) (φ) : CKForces cs5Mreach cs5Val cs5Bot s φ ↔ φ ∈ s.seg.head`,
      mirroring `cs4_truth_lemma` (`CS4.lean:457`). The atom/bot/imp/and/or cases are verbatim from
      CS4. The box-forward case is `box_reflect` as in CS4. The box-backward case is
      `cs5_box_backward` (this is the only case that differs materially — CS4 uses
      `box_refuting_theory` directly there, which is exactly what fails for CS5). The
      diamond-forward case uses `cs5Tail_dia_of_mem` and needs **no** `diaRefuting` segment and no
      exclusion parameter — CS5's diamond-backward case is free, unlike CS4's. The diamond-backward
      case uses `cs5_diam_witness` (Phase 6).
- [ ] Prove `cs5_completeness {φ} (h_valid : CKValidFC.{u, u} cs5FC'' φ) : Derivable CS5ModalAxiom φ`
      via `ckvalidFC_completeness` (`CKExtension.lean:187`, already abstract over `World` — no change
      needed), mirroring `cs4_completeness` (`CS4.lean:551`).
- [ ] Prove `cs5_soundness_completeness {φ} : Derivable CS5ModalAxiom φ ↔ CKValidFC.{u, u} cs5FC'' φ`,
      mirroring `cs4_soundness_completeness` (`CS4.lean:565`).
- [ ] Revise the `CS5.lean` module docstring to final status: completeness established, the route
      (frame condition weakening + symmetric tail + simultaneous pair construction), and the
      correction of 508's record. Cite `Pacheco2024` if his construction was used, `Simpson1994`
      Ch. 3 for the IS5 frame class that the canonical `r` realizes (it is a genuine equivalence
      relation), and `Wijesekera1990` for fallible worlds. Update `## Main Definitions`.
- [ ] Delete Phase 3's "the actual open problem is the box-backward case" paragraph, which Branch A
      makes obsolete. Keep `cs5_symmetric_tail_box_gap` as a landed theorem — it documents why the
      construction has the shape it does.

**Branch B — Phase 10 did not close** (mandatory fallback; **no `sorry`, no stub, no vacuous
definition**):

- [ ] State the obstruction as a **mechanized theorem**, not a comment. `cs5_symmetric_tail_box_gap`
      (Phase 5) already is one; strengthen it with whatever Phases 9-10 established — e.g. the
      precise saturation condition shown necessary, the point at which the pair poset fails, or
      Phase 8's refutation of the primeness step if that is what blocked.
- [ ] Land the three-world countermodel from `probes/cs5-boxgap-countermodel.lean` (`w3r_fc`,
      `w3_box_p_or_box_q_at_w`, `w3_not_box_p_at_w`, `w3_not_q_at_w`) into the library, so the
      non-vacuity of the gap is a library fact rather than a probe artifact.
- [ ] Revise the `CS5.lean` module docstring to state honestly: soundness over `cs5FC''` is
      established (all 17 axioms, axiom-free); the canonical frame conditions are established; the
      diamond cases are free; completeness is open **at the box-backward pair construction
      specifically**, with the mechanized theorem naming the obstruction. State what was tried and
      what would unblock. Do not restate or resurrect 508's claim — the obstruction is at a
      different place, and soundness is not in question.
- [ ] Do **not** mark CS5 completeness BLOCKED as a library-level verdict. It is open at a precisely
      located sub-problem, which is a materially different and much better-understood position than
      where 508 left it.

**Timing**: 2 hours

**Depends on**: 10

**Files to modify**:

- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` (and/or `CS5Canonical.lean`).

**Verification**:

- Full CI gate (as Phase 1): `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
  `lake lint`, `lake test`, `lake shake --add-public --keep-implied --keep-prefix`, plus
  `lake exe mk_all --module` if files were added.
- `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Constructive/` returns nothing.
- Zero-debt scan: no `def X := True`, `theorem X := trivial`, or any vacuous-definition pattern.
- Branch A: `#print axioms cs5_soundness_completeness` — record the axiom set (expect the Zorn
  three via `prime_set_exclusion`).
- Branch B: the obstruction theorem compiles, is non-vacuous (it has the countermodel as witness),
  and `#print axioms` is recorded.
- `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, `CKTruthLemma.lean` unmodified.

## Testing & Validation

- [ ] `lake build` — clean, no warnings introduced.
- [ ] `lake test` — `CslibTests/` passes.
- [ ] `lake exe checkInitImports` — every touched file imports `Cslib.Init`.
- [ ] `lake exe lint-style` — text linters pass.
- [ ] `lake lint` — environment linters pass (docBlame in particular: every new public declaration
      needs a docstring).
- [ ] `lake shake --add-public --keep-implied --keep-prefix` — no unused imports introduced.
- [ ] `lake exe mk_all --module` — run only if a new file was added (Phase 7 split, Phase 11).
- [ ] `grep -rn "sorry" Cslib/Logics/Modal/Metalogic/Constructive/` returns nothing at every phase
      boundary, not only at the end.
- [ ] `#print axioms` recorded for every new theorem. Hard gates: `cs5_axiom_sound''` and
      `cs5Tail_symm` must report **no axiom dependencies at all**; anything else is a transcription
      defect against the verified probes.
- [ ] Probe reproduction: `lake env lean specs/509_rescope_CK_CS5_constructive_completeness/probes/<file>.lean`
      exits 0 for all probes, old and new.
- [ ] Every BibKey cited in a docstring resolves in `references.bib`.
- [ ] `git diff --stat` shows `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, `CKTruthLemma.lean`
      untouched.

## Artifacts & Outputs

- `Cslib/Logics/Modal/Metalogic/Constructive/CKExtension.lean` — `cs5FC''`, `cs5FC_implies_cs5FC''`.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5.lean` — soundness over `cs5FC''`, the two
  derivability lemmas, the corrected module docstring, the symmetric tail and `CS5Segment`, the
  canonical frame conditions, and (Branch A) the truth lemma and completeness, or (Branch B) the
  mechanized obstruction.
- `Cslib/Logics/Modal/Metalogic/Constructive/CS5Canonical.lean` — only if Phase 7's size check
  triggers the split.
- `Cslib/Logics/Modal/Metalogic/Constructive/SegmentLindenbaum.lean` — list-splitting and
  finite-conjunction helpers; corrected `:18` docstring claim.
- `references.bib` — `Pacheco2024`, `ArisakaDasStrassburger2015`.
- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-primeness.lean` (new, Phase 8).
- `specs/509_rescope_CK_CS5_constructive_completeness/probes/cs5-pair-construction.lean` (new,
  Phases 9-10).
- `specs/509_rescope_CK_CS5_constructive_completeness/summaries/01_cs5-symmetric-tail-completeness-summary.md`.
- `specs/509_rescope_CK_CS5_constructive_completeness/.orchestrator-handoff.json` — updated per phase.

## Rollback/Contingency

- **Per-phase**: every phase ends green (full CI gate) and is committed separately as
  `task 509 phase {P}: {name}`. Any phase can be reverted with `git revert` without disturbing its
  predecessors.
- **Phase 7 is the safe point**: Phases 1-7 are a complete, self-contained, independently valuable
  increment — they refute and retire task 508's published negative result and build the canonical
  model up to the frame conditions. If Phases 8-11 fail entirely, revert only 8-11; the library is
  strictly better than before and no claim in it is false.
- **Phase 10 failure is not a rollback**: it triggers Phase 11 Branch B, which is a real deliverable
  (the obstruction as a mechanized theorem). Reverting Phases 9-10's probes is optional; they
  document what was tried.
- **Phase 8 refutation is not a rollback**: if Pacheco's primeness step is unsound for quasi-prime
  heads, that finding lands as a probe and is reported. Phase 9 then attempts the pair poset carrying
  primeness as an invariant instead of deriving it.
- **`references.bib` additions** are independently revertable and harmless if the citing prose is
  reverted with them.
- **Nothing in this plan modifies** `CS4.lean`, `CT.lean`, `CK.lean`, `Segment.lean`, or
  `CKTruthLemma.lean`, so tasks 501/508's landed assets cannot be damaged by any rollback here.
