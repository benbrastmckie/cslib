# Task 494 Research — IT / IS4 / IS5 as Modular Extensions of IK

**Agent**: cslib-research-hard-agent · **Session**: sess_1784011298_752245_494 ·
**Reference-grounding tier**: 1 (literature-backed) · **Zero-debt target**

## Summary (actionable)

- **Extend, don't rebuild.** The task-480 framework (`canonicalR`, `canonical_f1/f2`,
  `canonicalBModel`, `canonical_imp_property`) and task-492 IK template suffice. No new
  canonical-model machinery is needed; only per-axiom *positive* closure lemmas plus one small
  frame-condition-parametrized generalization of `IValid` / `ivalid_completeness`.
- **Both □ and ◇ forms are required** for every extension (Wijesekera1990: ◇ is not
  □-definable intuitionistically). IT = T□+T◇, IS4 = 4□+4◇, IS5 = **B□+B◇ (symmetry)**.
- **Adversarial finding (Deliverable 6):** axiomatize **IS5 via B (symmetry), NOT via the
  euclidean/5 axiom.** The classical `canonical_eucl`/`canonical_eucl_from_5`
  (`Metalogic/Completeness.lean:141,190`) are `by_contra` + `mcs_neg_of_not_mem` +
  double-negation proofs that **do not transfer** to prime theories (no negation-completeness).
  Symmetry closure is fully **positive** and transfers cleanly. Refl+trans+symm ⇒ equivalence
  relation ⇒ Simpson's IS5 frame class.
- **All three canonical-closure proofs are LOW risk** (positive, MP-closure only) under the B
  route. The only nontrivial *soundness* cases are 4□ and B□ (they relocate the witness via F1/F2,
  exactly like IK's `idb` case already does — `IK.lean:178-184`).

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| IT = IK + reflexivity; axioms □A→A and A→◇A | [Simpson1994] Ch. 3 (§3.3 correspondence) | `Cslib.Logic.Modal.ITModalAxiom` + `it_soundness_completeness` | Both box/diamond T needed; ◇ not □-definable |
| IS4 = IK + refl+trans; □A→□□A and ◇◇A→◇A | [Simpson1994] Ch. 3, Ch. 5 | `Cslib.Logic.Modal.IS4ModalAxiom` | 4□ soundness needs F2 relocation |
| IS5 = IK + refl+trans+**symm** (equiv rel); A→□◇A and ◇□A→A | [Simpson1994] Ch. 3 / IS5 | `Cslib.Logic.Modal.IS5ModalAxiom` | Use B (symmetry), NOT euclidean 5 (see Deliverable 6) |
| ◇ is not □-definable intuitionistically (⇒ two-clause R, both-form axioms) | [Wijesekera1990] | `canonicalR` two-clause (`CanonicalModel.lean:117`) | Already reflected in framework |
| Classical canonicity of T/4/5/B (pattern to mirror, not reuse) | [ChagrovZakharyaschev1997] Thm 2.43, Lemma 5.5 | `Metalogic/Completeness.lean:71,84,141,190` | Classical proofs are negation-based; intuitionistic must be positive |

BibKey verification: **all three verified** in `references.bib`
(`Simpson1994`:86 `@phdthesis`, `Wijesekera1990`:885 `@article`,
`ChagrovZakharyaschev1997`:75 `@book`). No additions needed.

## Deliverable 1 — Intuitionistic axiom schemes (Lean shapes)

Add these constructors (each `ITModalAxiom φ : Prop`, extending the 14 `IKModalAxiom`
constructors verbatim). All use the existing `Proposition.box`, `◇` (`Modal/Basic.lean`).

```lean
-- IT (reflexivity): add to IK constructors
| tBox (φ : Proposition Atom) : ITModalAxiom ((Proposition.box φ).imp φ)          -- □A → A
| tDia (φ : Proposition Atom) : ITModalAxiom (φ.imp (◇φ))                          -- A → ◇A

-- IS4 (reflexivity + transitivity): IT constructors +
| fourBox (φ : Proposition Atom) : IS4ModalAxiom ((Proposition.box φ).imp (Proposition.box (Proposition.box φ)))  -- □A → □□A
| fourDia (φ : Proposition Atom) : IS4ModalAxiom ((◇(◇φ)).imp (◇φ))               -- ◇◇A → ◇A

-- IS5 (equivalence, via B/symmetry): IS4 constructors +
| bBox (φ : Proposition Atom) : IS5ModalAxiom (φ.imp (Proposition.box (◇φ)))       -- A → □◇A
| bDia (φ : Proposition Atom) : IS5ModalAxiom ((◇(Proposition.box φ)).imp φ)       -- ◇□A → A
```

These are the Fischer-Servi-dual box/diamond pairs used by [Simpson1994]. **Do not** add
`◇A→□◇A` (classical 5); it is not the constructive S5 route (Deliverable 6).

## Deliverable 2 — Axiom ↔ frame-condition correspondence + Lean predicate shapes

Frame conditions are predicates on the accessibility relation `r` of a `BFrame`; they hold
*alongside* the always-present F1/F2 (`BFrame.f1/f2`). Semantically compatible: reflexive/
transitive/symmetric `r` co-exists with up/down confluence with no conflict (the canonical `r`
already satisfies F1/F2 and we prove the extra property of the *same* relation).

| Axiom pair | Frame condition on R | Lean predicate shape |
|-----------|----------------------|----------------------|
| T□ `□A→A`, T◇ `A→◇A` | **reflexive** `∀w, r w w` | `def Reflexive (r) := ∀ w, r w w` |
| 4□ `□A→□□A`, 4◇ `◇◇A→◇A` | **transitive** `∀w u v, r w u → r u v → r w v` | `def Transitive (r) := ∀ ⦃w u v⦄, r w u → r u v → r w v` |
| B□ `A→□◇A`, B◇ `◇□A→A` | **symmetric** `∀w u, r w u → r u w` | `def Symmetric (r) := ∀ ⦃w u⦄, r w u → r u w` |

Interaction with `≤` / heredity: the box clause of `BForces` quantifies `≤ ∘ r`
(`Birelational.lean:116`), so reflexivity of `r` gives `□A→A` by taking `w'=w` (≤-refl) then
`u=w` (r-refl). Diamond quantifies `r` alone, so `A→◇A` uses persistence
(`bforces_persistence`) across `≤` to keep `A` at each `w'≥w`. Symmetry-based soundness (below)
uses persistence + F1/F2, mirroring `idb`. Prefer Mathlib's `Reflexive`/`Transitive`/`Symmetric`
(they exist for `α → α → Prop`) to avoid new definitions — reuse check: use Mathlib names.

## Deliverable 3 — Soundness (frame-condition → axiom validity)

Extend `ik_axiom_sound`'s `cases` (`IK.lean:136-189`) with new cases, each given the frame
condition as a hypothesis. Requires a **frame-condition-parametrized validity** `IValidFC`
(Deliverable 5). Difficulty per case:

- **T◇ `A→◇A`**: trivial. `⟨w', hrefl w', hforce_A⟩` after persistence. **EASY.**
- **T□ `□A→A`**: `hbox w' (le_refl) w' (hrefl w')`. **EASY.**
- **4◇ `◇◇A→◇A`**: destructure `⟨u,hru,⟨t,hut,hAt⟩⟩`, return `⟨t, htrans hru hut, hAt⟩`. **EASY.**
- **4□ `□A→□□A`**: **moderate** — needs F2 to relocate (as `idb` does, `IK.lean:180-184`):
  given `r w' u`, `u≤u'`, `r u' t`, use `f2 : r w' u → u≤u' → ∃w'' , w'≤w'' ∧ r w'' u'`, then
  `htrans (r w'' u') (r u' t)` and apply the outer `□A`. Pattern already proven for `idb`.
- **B◇ `◇□A→A`**: `⟨u, hru, hboxA⟩`; `hsymm hru : r u w`; `hboxA u (le_refl) w (hsymm hru)`
  gives `A@w`. **EASY** (symmetry only).
- **B□ `A→□◇A`**: **moderate** — take `w'≥w`, `r w' u`; persistence `A@w'`; symmetry `r u w'`;
  witness `⟨w', hsymm hru, A@w'⟩`. Uses persistence + symmetry (no F-relocation needed). **EASY-MOD.**

The `ik_soundness` structural-induction wrapper (`IK.lean:197-222`) and `necessitation`/`mp`
cases are reused verbatim (frame condition threaded as an extra parameter).

## Deliverable 4 — Completeness: canonical closure feasibility (THE key new work)

`canonicalR w v := (∀φ, □φ∈w → φ∈v) ∧ (∀φ, φ∈v → ◇φ∈w)` (`CanonicalModel.lean:117`).
Every prime world is deductively closed, so **`canonical_imp_property`** (`TruthLemma.lean:99`:
`(φ→ψ)∈w → φ∈w → ψ∈w`) plus a one-line `axiom_mem` (`Axioms φ → φ∈w.val`, via
`w.property.1.2 [] φ ⟨.ax [] _ h⟩`) discharge all closure steps **positively**. Each clause:

### IT — canonical reflexivity `canonicalR w w`  ✅ LOW risk
- box `□φ∈w → φ∈w`: `axiom_mem (tBox φ)` gives `(□φ→φ)∈w`; `canonical_imp_property`. Done.
- dia `φ∈w → ◇φ∈w`: `axiom_mem (tDia φ)` gives `(φ→◇φ)∈w`; `canonical_imp_property`. Done.

### IS4 — canonical transitivity `canonicalR w v → canonicalR v u → canonicalR w u`  ✅ LOW
- box `□φ∈w → φ∈u`: `axiom_mem(fourBox)`+MP ⇒ `□□φ∈w`; box-clause `w→v` ⇒ `□φ∈v`;
  box-clause `v→u` ⇒ `φ∈u`.
- dia `φ∈u → ◇φ∈w`: dia-clause `v→u` ⇒ `◇φ∈v`; dia-clause `w→v` (ψ=◇φ) ⇒ `◇◇φ∈w`;
  `axiom_mem(fourDia)`+MP ⇒ `◇φ∈w`.

### IS5 — canonical symmetry `canonicalR w v → canonicalR v w`  ✅ LOW-MODERATE
- box `□φ∈v → φ∈w`: dia-clause `w→v` (ψ=□φ) ⇒ `◇□φ∈w`; `axiom_mem(bDia)`+MP (`◇□φ→φ`) ⇒ `φ∈w`.
- dia `φ∈w → ◇φ∈v`: `axiom_mem(bBox)`+MP (`φ→□◇φ`) ⇒ `□◇φ∈w`; box-clause `w→v` ⇒ `◇φ∈v`.

**Every step is a `canonical_imp_property` MP or a clause application — no `by_contra`, no
negation.** This is why the B route works where euclidean does not.

**Highest-risk closure proof:** IS5 symmetry-box (`□φ∈v→φ∈w`), because it is the one step that
routes a *box* membership back through the *diamond* clause (ψ=□φ). Still positive and one-line,
but it is the least obvious chaining; verify the `bDia` instance shape matches `◇(□φ)→φ` exactly.

**480/492 sufficiency:** `canonicalR`, `canonical_f1/f2`, `canonicalBModel`, `canonical_imp_property`,
`canonical_box/diamond_witness`, `modal_prime_exclusion` all reused unchanged. Only *new* lemmas
are the three closure proofs above + `axiom_mem` helper.

## Deliverable 5 — Modularity recommendation (reuse-first)

**Recommend: one small shared scaffold + three thin per-system files** (mirrors classical
`Systems/{T,S4,S5}`). The one genuine gap is that `IValid`/`ivalid_completeness` are hardwired
to the bare IK frame class (F1/F2 only) — extensions need a frame-condition slot.

**New file `Intuitionistic/Extension.lean` (scaffold, ~80-120 lines):**
1. `IValidFC (FC : (World→World→Prop)→Prop) φ` — copy of `IValid` (`Birelational.lean:193`)
   with one extra binder `(_fc : FC r)`. (Add alongside `IValid`; leave `IValid`/IK untouched —
   zero churn to 480/492.)
2. `ivalidFC_completeness` — copy of `ivalid_completeness` (`Completeness.lean:187`) adding
   hypothesis `(h_canonFC : FC (@canonicalR Atom Axioms))` and passing it into the `h_valid`
   application (`Completeness.lean:229-235`). This is a ~2-line diff over the existing proof.
3. `axiom_mem` helper (1 lemma).

**Three files `Intuitionistic/{IT,IS4,IS5}.lean`** each: axiom datatype (IK constructors +
new), `*_axiom_sound` (extend `ik_axiom_sound`), canonical-closure lemma (Deliverable 4),
`*_completeness` = `ivalidFC_completeness` instantiated with the closure lemma as `h_canonFC`,
`*_consistent`, `*_soundness_completeness`. IS4 imports IT machinery; IS5 imports IS4 (nested
extension, matching the axiom inclusion). Estimated ~200-300 lines each — one phase per file.

Do **not** attempt a single "generic extension" typeclass over frame conditions: the payoff is
small and it would obscure the three concrete instantiations that reviewers expect (classical
`Systems/` keeps them separate too).

## Deliverable 6 — Adversarial check on IS5 (intuitionistic subtlety)

**Confirmed:** intuitionistic S5 has inequivalent axiomatizations. Two candidate frame
conditions for the extra S5 strength:
- **Euclidean** `r w v ∧ r w u → r v u` — the classical `canonical_eucl_from_5` route from
  `◇A→□◇A`. **Rejected:** its canonical proof (`Metalogic/Completeness.lean:190-...`) is
  `by_contra` → `mcs_neg_of_not_mem` → `Axiom5` double-negation shuffling. Prime theories are
  **not** negation-complete (that is the whole point of using prime, not maximal-consistent,
  worlds — `CanonicalModel.lean:76-80`), so `mcs_neg_of_not_mem` has no intuitionistic analogue.
  Canonical euclideanness from `◇A→□◇A` is **NOT straightforward** — flag as blocked-if-attempted.
- **Symmetric** `r w v → r v w` from B□ `A→□◇A` + B◇ `◇□A→A`. **Accepted:** positive canonical
  closure (Deliverable 4). Refl (T) + trans (4) + symm (B) ⇒ **equivalence relation**, which is
  exactly Simpson's IS5 birelational frame class ([Simpson1994], IS5). Semantically an
  equivalence relation is euclidean, so soundness over the intended IS5 frame class is preserved;
  we simply never *prove canonical euclideanness* — we prove the three positive properties and
  bundle them.

**Recommendation:** IS5 = IK + T□ + T◇ + 4□ + 4◇ + B□ + B◇, frame class = reflexive ∧ transitive
∧ symmetric. This is the constructive, zero-debt route.

**Other flagged risks:** none blocked. 4□ and B□ soundness need F1/F2 witness relocation, but
the pattern is already proven in IK's `idb` case (`IK.lean:178-184`) — low risk, not a defect.

## Adversarial Self-Verification (H4)

- **Challenge: "reflexivity only needs □A→A."** Refuted — `canonicalR`'s dia clause
  `φ∈w→◇φ∈w` is not reachable from `□A→A` intuitionistically (Wijesekera1990: no interdefinition).
  Verified against the two-clause `canonicalR` (`CanonicalModel.lean:117`). Both T-forms required.
  Confidence: **high** (grounded in code, not memory).
- **Challenge: "reuse classical `canonical_eucl` for IS5."** Refuted by reading the classical
  proof (`Metalogic/Completeness.lean:141-210`): it depends on `mcs_neg_of_not_mem` /
  `by_contra`, unavailable for prime theories. Revised IS5 to the B/symmetry route.
  Confidence: **high.**
- **Challenge: "4□ soundness is trivial like 4◇."** Revised after tracing the `≤∘r` box clause:
  4□ needs F2 relocation (like `idb`). Documented as moderate, not easy. Confidence: **high**
  (mirrors an already-compiled proof).
- **Challenge: closure needs a new deductive-closure API.** Refuted — `canonical_imp_property`
  (`TruthLemma.lean:99`) + `w.property.1.2` already provide MP/derivation closure; only a
  one-line `axiom_mem` helper is new. Confidence: **high.**
- **BibKey status:** all three (`Simpson1994`, `Wijesekera1990`, `ChagrovZakharyaschev1997`)
  verified present in `references.bib`. Theorem numbers cited where the source is specific
  (CZ Thm 2.43 / Lemma 5.5); Simpson references are by chapter (thesis, no fine-grained numbering
  loaded — literature sub-index does not contain Simpson1994, so chapter-level citation retained).
- **Reuse Check Protocol:** all 5 steps run — Foundations/framework (`canonicalR`, witnesses,
  `canonical_imp_property`), typeclass reuse (Mathlib `Reflexive/Transitive/Symmetric`),
  no new notation, classical `Systems/` mirror pattern, and Logics namespace all checked.
- **Zero-debt:** no `sorry`/axiom/vacuous-def recommended; every obligation has a concrete
  positive proof route.

## Next steps

Run `/plan 494` (or `/plan 494 --hard`) to phase: (P1) `Extension.lean` scaffold
(`IValidFC` + `ivalidFC_completeness` + `axiom_mem`); (P2) `IT.lean`; (P3) `IS4.lean`;
(P4) `IS5.lean`. Each phase is one agent run (~200-300 lines), building on the prior.
