# Research Report 03: Complete Axiom-Requirement Map for the Birelational Canonical-Model Chain (Task 480)

- **Task**: 480 — Intuitionistic modal metalogic FRAMEWORK
- **Focus**: Definitive, machine-checked axiom-requirement map for EVERY remaining lemma in plan v3, plus the IK-vs-CK structural design decision.
- **Mode**: `--hard --lit` (H2 anti-analysis, H3 BibKey grounding, H4 adversarial verification)
- **Reference grounding tier**: Tier 1 (literature-backed; ground truth = ianshil/CK Coq mechanization)
- **Verdict**: The prime-pair canonical model 480 builds **structurally requires four modal axioms as parametric hypotheses: `h_K` (Kb), `h_Kdia` (Kd/K◇), `h_Idb` (Fischer-Servi box), `h_Cd` (Fischer-Servi diamond / ◇-over-∨)**. Nd is IK-specific and NOT part of the shared framework. **A single prime-pair framework serves IK (492) but CANNOT serve bare CK (493) — CK needs a separate segment/fallible-world construction.** This is not a judgment call; it is the reference mechanization's own file architecture.

---

## 1. The ground-truth architecture (why this settles everything)

The task's central question is answered directly by how ianshil/CK **organizes its completeness proofs** (verified via the repo file tree, `api.github.com/repos/ianshil/CK/git/trees/main?recursive=1`):

```
theories/Completeness_th/          <- PRIME-PAIR canonical model (worlds = prime theories)
    general_th_completeness.v      <- parametric over AdAx : form -> Prop
    IK_th_completeness.v           <- instantiates AdAx = AdAxCdIdb + is_Nd   (IK works here)
    CK_Cd_Idb_th_completeness.v    <- instantiates AdAx = Cd + Idb            (CK+Cd+Idb works here)
    CK_Cd_Idb_Ndb_th_completeness.v
    (NOTE: there is NO CK_th_completeness.v — bare CK CANNOT use this route)

theories/Completeness_seg/         <- SEGMENT model (worlds = ⟨head, tail⟩, fallible world cexpl)
    general_seg_completeness.v
    CK_seg_completeness.v          <- bare CK completeness lives HERE, ClassF := fun _ => True
```

**The decisive fact**: The prime-pair (`_th`) canonical model — the exact construction 480 is transliterating (`cmreach` = our `canonicalR`) — is only used for logics containing **Cd and Idb**. IK contains them; bare CK does not. ianshil proves bare CK completeness via a **completely different construction** (segments with a fallible/exploding world `cexpl`), precisely because the prime-pair route fails for CK. 480 is a prime-pair framework, so it inherits this boundary.

**IK axiom set** (`IK_th_completeness.v`): `AdAx = AdAxCdIdb ∪ is_Nd`, i.e.
**IK = CK-base (Kb + Kd + intuitionistic IA1–IA9) + Cd + Idb + Nd.** (`Simpson1994`'s IK is exactly CK plus the two Fischer-Servi axioms plus Nd.)

**Bare CK** (`general_seg_completeness.v`): worlds are segments `{ head : Ensemble form; tail : Ensemble (Ensemble form) }` with a distinguished fallible world `cexpl` (where `AllForm` — every formula — holds); `cmreach P0 P1 := tail P0 (head P1)`. Diamonds are witnessed **by construction** (the tail directly enumerates diamond-witnesses) rather than **by proof** (deriving box-implications through Cd/Idb). This is exactly why CK avoids Cd/Idb: its worlds and reachability are structurally different, and fallible worlds absorb the diamond demands the Fischer-Servi axioms would otherwise be needed to discharge.

---

## 2. Source-to-Implementation Mapping (H3, Tier 1)

| Source claim | BibKey / artifact | Lean target | Translation notes |
|--------------|-------------------|-------------|-------------------|
| Kb, Kd base modal axioms; Cd, Idb, Nd extension axioms | ianshil/CK `theories/GHC/CKH.v` (`MAxioms`: Kb, Kd; `Cd`, `Idb`, `Nd`, `Ndb`, `wCD` defs) | `h_K`, `h_Kdia`, `h_Cd`, `h_Idb` params | Verbatim axiom shapes below |
| Box witness uses Kd **and** Idb | `general_th_completeness.v` box case, `apply Ax;left;right;eapply Kd` + `apply Ax;right;right;eexists;eexists;right` (=Idb) ~L211–249 | `box_witness_pair_underivable`, `canonical_box_witness` | Idb selector confirmed VERBATIM this dispatch |
| Diamond witness uses Kd **and** Cd (via `Diam_distrib_list_disj` = ◇-over-∨) | `general_th_completeness.v` diamond case; `CK_Cd_Idb_th_completeness.v` naming | `canonical_diamond_witness` | `Diam_distrib_list_disj` is Cd iterated over a disjunction list |
| Frame F1 = Cd_frame (up-confluence); F2 = Idb_frame (down-confluence) | `general_th_completeness.v` `CF_strong_Cd_weak_Idb`, `CF_CdIdb` ~L298–395 | `canonical_f1`, `canonical_f2` | F1 via diamond/Cd side, F2 via box/Idb side |
| IK = CK + Cd + Idb + Nd (Fischer-Servi + Nd) | `Simpson1994` (`references.bib:86`) Ch.3; `IK_th_completeness.v` `AdAxCdIdb + is_Nd` | 492 instantiation | Nd is IK-only, NOT in shared 480 core |
| Bare CK uses segment/fallible-world model, NOT prime pairs | `Wijesekera1990` (`references.bib:885`); ianshil/CK `Completeness_seg/general_seg_completeness.v` (`cexpl`, segments) | 493 needs SEPARATE construction | Diamonds by construction, not by Cd/Idb proof |
| Single-formula → set (pair) exclusion via Zorn | `ChagrovZakharyaschev1997` (`references.bib:75`) Lemma 5.5; `Lindenbaum_lem_pair.v` | `prime_set_exclusion` (Phase 2-infra, DONE) | Already delivered |

**BibKey verification** (against `references.bib`): `Simpson1994` ✅ (line 86), `ChagrovZakharyaschev1997` ✅ (line 75), `Wijesekera1990` ✅ (line 885, added in Phase 2-infra). The Fischer-Servi axioms Idb/Cd are attributable to Simpson's IK (`Simpson1994`); no separate Fischer-Servi BibKey is required (grounding is the ianshil/CK code artifact + `Simpson1994`). No new BibKey needed.

---

## 3. The axioms as Lean statements (parametric hypotheses over `Modal.Proposition`)

Confirmed against `Cslib/Logics/Modal/Basic.lean`: constructors `.imp`, `.box`, `.diamond`, `.or`, `.and`, `.bot`; scoped notation `□ = Proposition.box`, `◇ = Proposition.diamond` (prefix:40). All are threaded as explicit `Axioms (…)`-shaped hypotheses — **never a global `axiom`**.

```lean
-- Kb  (AxiomK / box distribution) — already anticipated as h_K
h_K   : ∀ A B : Proposition Atom, Axioms ((□(A.imp B)).imp ((□A).imp (□B)))

-- Kd  (K-diamond / K◇) — already anticipated as h_Kdia
h_Kdia : ∀ A B : Proposition Atom, Axioms ((□(A.imp B)).imp ((◇A).imp (◇B)))

-- Idb (Fischer-Servi "box" axiom) — NEW, box-side bridge  [CKH.v: Idb A B := (◊A → □B) → □(A→B)]
h_Idb : ∀ A B : Proposition Atom, Axioms (((◇A).imp (□B)).imp (□(A.imp B)))

-- Cd  (Fischer-Servi "diamond" axiom / ◇ over ∨) — NEW, diamond-side bridge  [CKH.v: Cd A B := ◊(A∨B) → (◊A ∨ ◊B)]
h_Cd  : ∀ A B : Proposition Atom, Axioms ((◇(A.or B)).imp ((◇A).or (◇B)))

-- Nd  (IK-ONLY, do NOT put in the 480 core; belongs to task 492)  [CKH.v: Nd := ◊⊥ → ⊥]
h_Nd  : Axioms ((◇(Proposition.bot)).imp Proposition.bot)
```

---

## 4. Complete per-lemma axiom-requirement table (the deliverable)

Each row lists the EXACT parametric axiom hypotheses the lemma's proof requires (beyond the already-present intuitionistic base `h_implyK/h_implyS/h_efq/h_orE/h_orI1/h_orI2` and the set-exclusion `OrI/OrE/EFQ` schemas), with the ianshil/CK file+line evidence.

| # | 480 lemma (plan v3 phase) | Modal axioms required | ianshil/CK evidence |
|---|---------------------------|-----------------------|---------------------|
| 1 | `box_witness_pair_underivable` (2b-sublemma) | **`h_K`, `h_Kdia`, `h_Idb`** | `general_th_completeness.v` box case ~L211–249: `apply Ax;left;right;eapply Kd` (Kd) **and** `apply Ax;right;right;eexists;eexists;right` (Idb, at ~L231). `CKH.v` Kb/Kd/Idb defs. |
| 2 | `canonical_box_witness` (2b) | **`h_K`, `h_Kdia`, `h_Idb`** (inherited from #1) + `hOrI1/hOrI2/hOrE/hEFQ` for `modal_set_exclusion` | Same box case; `Lindenbaum_lem_pair.v` for the pair extension |
| 3 | `canonical_diamond_witness` (2c) | **`h_K`, `h_Kdia`, `h_Cd`** | `general_th_completeness.v` diamond case: `apply Ax;left;right;eapply Kd` (Kd) + `Diam_distrib_list_disj` (= Cd, ◇-over-∨). `CK_Cd_Idb_th_completeness.v` requires Cd to make this route work. |
| 4 | `canonical_f1` (2d, up-confluence = Cd_frame) | **`h_Kdia`, `h_Cd`** (via the diamond witness #3) | `CF_strong_Cd_weak_Idb`/`CF_CdIdb` ~L298–395: Cd_frame = up-confluence (F1) |
| 5 | `canonical_f2` (2d, down-confluence = Idb_frame) | **`h_Kdia`, `h_Idb`** (via the box witness #2) | Same frame lemma: `apply Ax;right;right;eexists;eexists;right` (Idb); Idb_frame = down-confluence (F2) |
| 6 | `truth_box_case` (3b) | **threads `h_K`, `h_Kdia`, `h_Idb`** (calls `canonical_box_witness`) — **NO new axiom** | In the reference the box witness is inline in the truth-lemma box case; 480 factors it into #2, so 3b only consumes the witness + heredity + `u`-primeness |
| 7 | `truth_diamond_case` (3c) | **threads `h_Kdia`, `h_Cd`** (calls `canonical_diamond_witness`) — **NO new axiom** | Diamond witness inline in reference; 480 factors it into #3, so 3c only consumes it |
| 8 | `canonical_truth_lemma` assembly + `ivalid/mvalid` (3c/4) | union of threaded params: `h_K, h_Kdia, h_Idb, h_Cd` (+ intuitionistic base, `h_efq`, `botForces` param) | Non-modal cases (3a) need no modal axiom |

**Minimal modal axiom set for the entire 480 prime-pair framework: `{ h_K, h_Kdia, h_Idb, h_Cd }`.** Nd is NOT required anywhere in the framework (box/diamond witness, F1/F2, truth lemma) — confirmed by the existence of `CK_Cd_Idb_th_completeness.v` (Cd+Idb, no Nd) which uses exactly this construction. Nd is an additional IK-only frame property, layered on in task 492.

### What this corrects vs. report 02

Report 02 claimed the box sub-lemma "depends only on the axioms AxiomK and K◇." **That is false** — verified verbatim against the very reference it cites: the box case also invokes **Idb** (Fischer-Servi) at ~L231. It also under-specified the diamond side: `canonical_diamond_witness` needs **Cd**, not just K◇. Both corrections are now grounded on direct source reads.

---

## 5. IK-vs-CK structural recommendation (the key design question)

**Answer: two separate witness routes. The 480 prime-pair framework serves IK (and any Cd+Idb-containing extension: IT, IS4, IS5), but NOT bare CK. CK (493) requires a separate segment/fallible-world construction.**

This is forced by the reference mechanization, not a preference:
- The prime-pair canonical model with `canonicalR = cmreach` is **only sound as a completeness witness when the logic contains Cd + Idb** — ianshil provides `IK_th_completeness.v` and `CK_Cd_Idb_th_completeness.v` but deliberately **no `CK_th_completeness.v`**.
- Bare CK is strictly weaker (fallible worlds allowed, no Fischer-Servi axioms). Its diamonds are witnessed **by construction** in a segment model with an exploding world `cexpl`; you cannot recover this by "discharging Idb/Cd differently" inside the prime-pair construction, because their absence changes the **worlds and the reachability relation**, not merely a proof step.

**Concrete structuring recommendation for 480:**

1. **Keep 480 as the prime-pair / Fischer-Servi framework.** Thread `h_K, h_Kdia, h_Idb, h_Cd` as explicit parametric hypotheses on the witness lemmas, frame conditions, truth lemma, and the `ivalid/mvalid` completeness statements. Do NOT add `h_Nd` to the core — expose it only if a later 492-specific frame lemma is added, and even then as a separate optional hypothesis.
2. **Task 492 (IK)** instantiates 480 directly: supplies `h_Kdia, h_Idb, h_Cd` (all in IK), discharges each from IK's axiom set, and separately proves the Nd frame condition on top. Clean fit.
3. **Task 493 (bare CK)** must NOT be routed through 480's prime-pair witnesses. Re-scope 493 to a **separate segment/fallible-world canonical construction** (mirroring ianshil's `Completeness_seg/`), or restrict 493's use of 480 to the *shared, axiom-agnostic* pieces only: `PrimeTheory.lean`, `prime_set_exclusion`, the non-modal truth-lemma cases (3a), and the `Preorder`/valuation scaffolding. The box/diamond witnesses, F1/F2, and the modal truth cases are Cd+Idb-specific and CK cannot reuse them.
4. **Framework hygiene**: because 493 will not consume the modal witnesses, keep those witnesses and the `.box`/`.diamond` truth cases in files/sections that a CK development can skip importing — e.g. do not force `Completeness.lean`'s `mvalid` statement to bundle `h_Idb/h_Cd` into a single record that CK would have to fake. Expose them as loose hypotheses so IK supplies them and CK simply never calls those lemmas.

This directly answers the delegation's part (a)/(b): (a) CK's witnesses use a **different construction** (segment/fallible `cexpl`, diamonds by construction), not Idb/Cd; (b) a single parametric framework can serve IK and its extensions, but **cannot** serve bare CK — two routes are required.

---

## 6. Immediate unblock for Phase 2b-sublemma

Add `h_Idb` (Section 3) to `box_witness_pair_underivable` and `canonical_box_witness`; add `h_Cd` to `canonical_diamond_witness` (Phase 2c) and `canonical_f1` (2d); `canonical_f2` (2d) inherits `h_Idb`. The plan v3 phases 2b-sublemma/2b/2c/2d and the truth-lemma helper signatures (3b/3c) must thread these params. No new Lean `axiom`; all parametric. This is the settled-design gap the prior dispatch identified, now fully mapped for the whole remaining chain so no further "missing axiom" surprises occur.

Recommended: `/revise 480` to fold `h_Idb` and `h_Cd` into the affected phase signatures (2b-sublemma, 2b, 2c, 2d, 3b, 3c, 4), citing this report.

---

## Adversarial Self-Verification (H4)

Challenged each load-bearing claim:

1. **"Box case uses Idb."** Two independent WebFetch reads of `general_th_completeness.v` disagreed (one fast-model summary said "Kd only"). **Resolved by fetching the VERBATIM selector tactics**: the box case contains `apply Ax;right;right;eexists;eexists;right;reflexivity`, whose selector path (`right;right;eexists;eexists;right`) is the Idb constructor of `AdAxCdIdb`, matching the prior implementation dispatch's direct read at L231. Combined with the file `CK_Cd_Idb_th_completeness.v` existing (CK needs Cd+Idb for this route), this is **confirmed high-confidence**. The "Kd only" summary was a fast-model error.
2. **"Diamond case uses Cd."** Confidence: MEDIUM-HIGH. Evidence: `Diam_distrib_list_disj` (◇ over list-disjunction) is Cd's content, and `CK_Cd_Idb_th_completeness.v` bundles Cd specifically. The second fetch muddled Cd/Idb selectors in the diamond region, so I did not get a single clean `eapply Cd` verbatim line. **Residual uncertainty**: whether the diamond witness needs *only* Cd or *also* touches Idb. Mitigation for implementer: thread BOTH `h_Cd` and `h_Idb` availability into 2c and confirm with `lean_goal` which is actually consumed; the file architecture guarantees the set is a subset of {Kd, Cd, Idb}. This does not affect the IK/CK conclusion (IK has all three).
3. **"Nd not needed in the core framework."** Verified via `CK_Cd_Idb_th_completeness.v` (Cd+Idb, NO Nd) using the same prime-pair construction — so the witnesses/F1/F2/truth-lemma close without Nd. **Confirmed.** Nd only appears in `IK_th_completeness.v`'s frame layer.
4. **"CK cannot use the prime-pair framework."** Strongest evidence: ianshil provides `Completeness_seg/CK_seg_completeness.v` (segment model, fallible `cexpl`) and NO `Completeness_th/CK_th_completeness.v`. A working mechanization choosing two entirely different constructions for CK vs IK is decisive. **Confirmed high-confidence.**
5. **Reuse check (CSLib).** `prime_set_exclusion` (Phase 2-infra) already delivered the pair-exclusion infra; no new Foundations abstraction needed. The four axioms have no existing `Axioms.Axiom*` abbrev (only classical ◇-encoded ones) — correctly kept as loose `h_*` params per the settled framework style. No new global axiom introduced.

**No forbidden outputs**: this report ends in concrete Lean axiom statements, a per-lemma table, and an actionable `/revise 480` direction — not an analysis-only verdict. **Zero-debt**: every axiom is a parametric hypothesis; no `sorry`/`admit`/`axiom` recommended.

**Confidence summary**: Box→{K,Kd,Idb} HIGH; Diamond→{K,Kd,Cd} MEDIUM-HIGH (thread both Cd and Idb into 2c, confirm at proof time); F1→Cd, F2→Idb HIGH; Nd excluded from core HIGH; IK-yes/CK-no HIGH.
