# Research Report: Verified Build-Grounded Fix Mapping for Modal.Tableau.Soundness Drift

- **Task**: 364 - modal_tableau_soundness_drift_repair
- **Started**: 2026-06-27T23:55:00Z
- **Completed**: 2026-06-28T00:12:34Z
- **Effort**: ~1.5h research (hard-mode, build-grounded + adversarial verification)
- **Dependencies**: None
- **Sources/Inputs**:
  - `Cslib/Logics/Modal/Tableau/Soundness.lean` (948 lines; read slices 92-202, 202-386, 798-947)
  - **Actual scoped build**: `lake build Cslib.Logics.Modal.Tableau.Soundness` (full 1607-line error log captured; 68 errors, 14 warnings) — the decisive ground truth
  - `Cslib/Logics/Modal/Basic.lean` (lemma existence: `Satisfies.neg_iff`, `diamond_iff`, `box_iff_forall`, `Proposition.neg_def`)
  - `Cslib/Foundations/Logic/Tableau/Sign.lean` (`Sign.isPos`, `isNeg_eq_not_isPos`)
  - `lean_loogle` verifications: `List.flatMap`, `List.mem_zip`, `List.mem_cons_self`, `Bool.or_eq_true`, `List.of_mem_zip`, `List.mem_iff_get`
  - git history (commits `396c9435`, `c299dfdc`)
  - Prior reports `01_drift-diagnosis.md`, `02_refactor-strategy.md`
- **Artifacts**: `specs/364_modal_tableau_soundness_drift_repair/reports/03_verified-fix-mapping.md`
- **Standards**: status-markers.md, artifact-management.md, tasks.md, report-format.md

## Executive Summary

- **The prior reports' central factual claim is REFUTED by the actual build.** Report 02 states "~68 remaining errors **ALL inside** `modalStepBranch_preserves_sat`." The real `lake build` shows ~15 distinct error sites lie in the **downstream** lemmas `modalExpandBranches_closed_unsat` (804-900) and `modalTableau_sound` (925-935) — a region **neither prior report diagnosed**. These have their own, separate Mathlib-drift root causes.
- **A new keystone error the prior reports missed: line 804 `branches.bind id`.** `List.bind` was removed from core/Mathlib (replaced by `List.flatMap`). This poisons the induction hypothesis `ih` with `accFreshInv sorry acc`, which cascades into most of the `HAppend`-synthesis and `unsolved goals` errors at 869/870/882/899/900. Fixing 804 first is likely to collapse the largest single block of downstream errors.
- **The Family-3 `hnewBs` failure has TWO distinct sub-modes**, not one. (a) *Flat-vs-nested conjunction drift* (boxPos): `simp` now normalizes `hsf` to a **right-associated** `A ∧ B ∧ C`, so the nested `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩` fails — fix is `obtain ⟨hnewBs, _, hnewAcc⟩`. (b) *Recognizer-no-longer-reduces drift* (negPos 276, negNeg 625): `simp` leaves an un-reduced `match (if … modalNegOf? …)` term, so `obtain`/`cases` hits a non-inductive — fix requires strengthening the simp set to evaluate the `modalNegOf?/modalImpOf?/modalOrOf?` recognizers. The build log's goal/term dumps reveal both shapes **for free** (no `lean_goal` needed).
- **A pervasive mechanical fix the prior reports under-counted: `List.mem_cons_self _ _` (14 sites).** Its signature changed to all-implicit (`{a} {l} : a ∈ a :: l`); every `List.mem_cons_self _ _` must drop the `_ _`. Only line 875 currently errors because the other 13 sites are shadowed by earlier failures — they **will surface** as each case's primary error is cleared.
- **Line 747 `Duplicate alternative name imp` is a genuine structural error** (the degenerate second `imp` arm), not a drift artifact — it must be fixed regardless and is independent of the simp drift.
- **All lemmas the prior reports recommend exist and are correctly named** (`Satisfies.neg_iff/diamond_iff`, `Proposition.neg_def`, `Sign.isPos`, `Proposition.beqToEq`), **except** the prior claim that "there is no characterization lemma" for `Sign.isPos` — `Sign.isNeg_eq_not_isPos` does exist. **Recommendation: the report-02 10-sub-lemma refactor is NOT necessary for this drift repair and is over-engineered** (see Decisions); a build-log-driven, in-place, commit-per-cluster repair is faster and lower-risk.

## Context & Scope

The file `Cslib/Logics/Modal/Tableau/Soundness.lean` (948 lines, toolchain `leanprover/lean4:v4.31.0`) is sorry-free (`grep` confirms zero `sorry`/`admit`) and was the lone module left unrepaired in the 2026-06-26 CI sweep. Current HEAD `30f46c20`; the file's last task-364 commit is `396c9435` ("restore to best-known state (Phase 1 complete, 68 errors)"). `Proposition.beqToEq` (line 78) and the `modalClosed_unsat` repair (lines 100-155) from Phase 1 are present and — confirmed by the build — **compile cleanly** (no errors in lines 80-156).

Scope of this report: verify the prior diagnoses against the *actual* build, map every error cluster to a source location + fix idiom + confidence, audit recommended lemma names, and deliver a chunked repair ordering. I deliberately avoided `lean_goal` entirely: the captured `lake build` error log already dumps goal states at every `unsolved goals` site (228, 870, 900, 925) and the un-reduced term at `cases failed` sites (276), which is sufficient grounding and sidesteps the context-overflow trap that defeated three prior agents.

## Findings

### 1. Verified Error-Cluster Mapping Table

68 raw errors collapse to the distinct clusters below. "Repeats" = the same site re-reported by Lean's elaborator (e.g. 304/336/363 each appear 3×; 650/706/730 each 3×).

| # | Error cluster (count) | Source `file:line` | Root cause | Recommended fix idiom | Status |
|---|---|---|---|---|---|
| C1 | `unsolved goals` + `No goals to be solved` (2) | `Soundness.lean:228-229` (boxPos) | `simp [tryAllPropRules…] at hsf` now reduces further; the `split_ifs … with hemp` bullet structure (227-231) misaligns and `hsf` is already a flat `A ∧ B ∧ C` | Collapse 227-231: after `simp only [Option.some.injEq, Prod.mk.injEq] at hsf`, use `obtain ⟨rfl, _, rfl⟩ := hsf` (flat). Handle empty-`boxPropagation` case via `hemp`/`simp` separately | **VERIFIED** (build dumps `hsf : [boxPropagation b acc φ lbl ++ b] = newBs ∧ [e] = newExps ∧ acc = newAcc` at 228) |
| C2 | `cases failed: Dependent elimination` (negPos) (1) | `Soundness.lean:276` | `simp` left `hsf` as an un-reduced `match (if (match a→⊥ with …modalNegOf?/modalOrOf?…))`; `obtain` (=`cases`) hits a non-inductive | Strengthen simp set so the `modalNegOf?/modalImpOf?/modalOrOf?` recognizers + `if` reduce to a `RuleResult`; then `obtain ⟨rfl, _, rfl⟩ := hsf`. May need `decide := true` in simp config or explicit recognizer-unfold lemmas | **VERIFIED root** (build dumps the un-reduced `match`/`if` term); fix idiom MEDIUM |
| C3 | `Unknown identifier hnewBs` ×3 each (pos: 304, 336, 363) | orPos 304, impPos 336, impPosGen 363 | The `obtain ⟨⟨hnewBs,_⟩,hnewAcc⟩ := hsf` fails → `hnewBs` unbound → every later `subst hnewBs` errors | Same as C1/C2 per case: replace nested `⟨⟨hnewBs,_⟩,hnewAcc⟩` with flat `⟨hnewBs, _, hnewAcc⟩` (or `⟨rfl,_,rfl⟩`); fix the upstream `simp` shape if a `match` remains | **VERIFIED cause**; idiom HIGH for flat-conjunction sub-mode, MEDIUM if a `match` persists |
| C4 | `Unknown identifier hnewBs` (boxNeg) (1) | `Soundness.lean:403` | Same `obtain` failure at boxNeg entry | Same flat-obtain idiom | **VERIFIED cause** |
| C5 | `cases failed` (negNeg) (1) | `Soundness.lean:625` | Same as C2 (neg branch) | Same as C2 | **VERIFIED root**, idiom MEDIUM |
| C6 | `Unknown identifier hnewBs` ×3 each (neg: 650, 706, 730) | orNeg 650, impNeg 706, impNegGen 730 | Same as C3 (neg branch) | Same as C3 | **VERIFIED cause** |
| C7 | `Duplicate alternative name imp` (1) | `Soundness.lean:747` | Genuine structural error: `cases formula` has two `| imp …` arms (the degenerate diamond-negation arm) | Rename/merge the second arm (e.g. `| imp φ bot2 =>` must not duplicate the earlier `| imp a c =>`); restructure as nested `cases` or guard. NOT a drift artifact | **VERIFIED** (structural; independent of simp drift) |
| C8 | **`Invalid field bind` (KEYSTONE)** (1) | `Soundness.lean:804` | `List.bind` removed from core; `branches.bind id` no longer elaborates → becomes `sorry` and poisons `ih`/`hInv` with `accFreshInv sorry acc` | `branches.flatMap id` (verified `List.flatMap : (α → List β) → List α → List β`) | **VERIFIED** (loogle: `List.flatMap` exists; `List.bind` absent) |
| C9 | `List.mem_zip` unknown + over-destructure + `Unknown identifier b` (821-828) (≈4) | `Soundness.lean:821-828` (zero-fuel case) | `List.mem_zip` removed; `obtain ⟨i,hi,hbi⟩ : ∃ i, branches.get i = b` over-destructures (∃ has 2 components, not 3); cascading `Unknown identifier b` | Reconstruct the `(b, expandedSets.get …) ∈ branches.zip expandedSets` proof without `List.mem_zip`. `List.of_mem_zip` is the *reverse* direction (mem→∧). Use `List.mem_iff_getElem`/indexing or a zip-membership constructor; fix obtain to 2 binders | **VERIFIED roots** (`List.mem_zip` absent via loogle; `List.mem_iff_get` still exists); exact fix MEDIUM — messiest block, needs a probe |
| C10 | `modalClosed_unsat bp hcl acc hsat` type mismatch `b` vs `bp` (1) | `Soundness.lean:858` | Likely cascade from C9 (the `bp`/`hsat` threading in the `key` suffices broke); `modalClosed_unsat` takes 3 args, the extra `hsat` mismatches | Re-derive once C8/C9 fixed; `modalClosed_unsat bp hcl acc` already has type `¬branchSatisfiable bp acc` — drop the spurious `hsat` or thread the correct satisfiability hyp | UNVERIFIED (probably cascade); re-check after C8/C9 |
| C11 | `HAppend` synth failures + `unsolved goals` (869, 870, 882, 899, 900) (≈5) | `Soundness.lean:869-900` | Cascade from C8: poisoned `ih`/`hlen_rec` give terms typed `List (List (List …))` (extra nesting) → `HAppend` can't resolve; `hlen_rec`/length goals reference `sorry ()` | Re-build after C8 fix; most should clear. Residual length goals: `simp [List.length_append, hdlength, hlength]` | UNVERIFIED (cascade hypothesis HIGH; confirm by rebuild after C8) |
| C12 | `List.mem_cons_self _ _` "Function expected" (1 now, **14 total**) | `Soundness.lean:875` now; also 233, 279, 311, 322, 341, 350, 368, 377, 433, 627, 651, 709, 732 | Signature changed to all-implicit `{a} {l} : a ∈ a :: l`; the `_ _` applies it as a function | Drop the args: `List.mem_cons_self`. Pervasive — apply at all 14 sites | **VERIFIED** (loogle: `List.mem_cons_self {a} {l} : a ∈ a :: l`) |
| C13 | `Bool.or_eq_true.mp` unknown + `rcases failed` (892) (2) | `Soundness.lean:892` | `Bool.or_eq_true` is a **propositional `Eq`** (`((a||b)=true) = (a=true ∨ b=true)`), not an `Iff`, so `.mp` doesn't exist | `rw [Bool.or_eq_true] at hedge` then `rcases hedge with h' | h'` (or `simp only [Bool.or_eq_true] at hedge`) | **VERIFIED** (loogle: type is `… = …`, not `↔`) |
| C14 | type mismatch `hstep2` newAcc/acc (896) (1) | `Soundness.lean:896` | Cascade from C8 poisoning (the `hstep` IH argument's `acc` got `sorry`-substituted) | Re-check after C8 | UNVERIFIED (cascade) |
| C15 | `unsolved goals` `m.r ((fun x=>w) w1) ((fun x=>w) w2)` with `hedge : false = true` (925) (1) | `Soundness.lean:925` | `simp only [Accessibility.empty, hasEdge, List.any_nil] at hedge` no longer closes the goal from the false hypothesis | Append `exact absurd hedge (by simp)` or change to `simp at hedge` (closes via `false = true`) | **VERIFIED** (build dumps goal + `hedge : false = true`) |
| C16 | `Unknown identifier modalExpandBranches_closed_unsat` (935) (1) | `Soundness.lean:935` | **Pure cascade**: the lemma at 798 failed to compile, so its name isn't registered | Auto-resolves once 798 (C8-C11) compiles | **VERIFIED cascade** |

**Region split (refutes report 02's "all in one theorem"):**
- `modalStepBranch_preserves_sat` (186-787): clusters C1-C7 (~12 distinct sites + the 14× `mem_cons_self` that mostly surfaces later).
- `modalExpandBranches_closed_unsat` (798-900): clusters C8-C14 (~15 errors; **undiagnosed by prior reports**).
- `modalTableau_sound` (917-945): C15 (genuine) + C16 (cascade).

### 2. Lemma Existence Audit (H4)

| Name (recommended by) | Exists? | Signature / note | Verdict |
|---|---|---|---|
| `Satisfies.neg_iff` (rpt 01/02) | YES | `Basic.lean:152` `Satisfies m w (¬φ) ↔ ¬Satisfies m w φ` | USE AS-IS |
| `Satisfies.diamond_iff` (rpt 01/02) | YES | `Basic.lean:156` | USE AS-IS |
| `Satisfies.box_iff_forall` (rpt 02) | YES | `Basic.lean:235` | USE AS-IS |
| `Proposition.neg_def` (rpt 01/02) | YES | `Basic.lean:103` `@[simp] … = .imp φ .bot := rfl` | USE AS-IS |
| `Sign.isPos` (rpt 01) | YES | `Sign.lean:76` `def isPos : Sign → Bool` | USE AS-IS |
| "no characterization lemma for `Sign.isPos`" (rpt 01 claim) | FALSE | `Sign.isNeg_eq_not_isPos` exists (`Sign.lean:87`) | **REFUTED** (minor; the inline `cases h : sign` idiom still works) |
| `Proposition.beqToEq` (rpt 02) | YES | `Soundness.lean:78` private def, in-scope | USE AS-IS for Family-4 |
| `LawfulBEq.eq_of_beq` (rpt 01 Family-4) | YES but fragile | still referenced at 149 for `WorldIndex` (compiles); fails for `Proposition Atom` (no instance) — that's why `beqToEq` exists | Use `beqToEq` for `Proposition`, `LawfulBEq.eq_of_beq` only for `WorldIndex`/`Nat` |
| `List.flatMap` (this report) | YES | `(α→List β)→List α→List β` (Init.Prelude) | replaces `List.bind` (C8) |
| `List.bind` (used at 804) | **NO** | removed from environment | must change |
| `List.mem_cons_self` (used 14×) | YES, **new sig** | `{a}{l} : a ∈ a :: l` (all implicit) | drop `_ _` (C12) |
| `List.mem_zip` (used at 823) | **NO** | loogle "no results" | `List.of_mem_zip` is reverse direction; reconstruct (C9) |
| `List.of_mem_zip` | YES | `(a,b) ∈ l₁.zip l₂ → a ∈ l₁ ∧ b ∈ l₂` | only mem→∧ direction |
| `List.mem_iff_get` (used at 821) | YES | `a ∈ l ↔ ∃ n, l.get n = a` | still valid; obtain over-destructures (2 vs 3) |
| `Bool.or_eq_true` (used 438, 892) | YES, **Eq not Iff** | `((a||b)=true) = (a=true ∨ b=true)` | OK as simp lemma (438); `.mp` invalid (892, C13) |

### 3. Assessment of the Two Prior Reports

**Report 01 (`01_drift-diagnosis.md`) — partially correct, materially incomplete.**
- Family 1 (`cases X.sign`): the closed-branch sites it targeted (99, 124) are **already fixed** (Phase 1 / `modalClosed_unsat` compiles). The idiom `cases h : sf.sign <;> simp_all [Sign.isPos]` is sound and matches the committed fix at 119-121. HOLDS, but already applied.
- Family 2 (`simp only [Satisfies]` ordering): plausible and the recommended lemmas exist, but in the current build **no Family-2 error fires** in the closed-branch cluster (it's fixed); the residual `simp only [Satisfies] at hpos/hneg` calls inside `modalStepBranch` are shadowed by the upstream `obtain` failures and are unverified until those clear. PARTIALLY HOLDS / DEFERRED.
- Family 3: directionally correct ("simp normalization drift") but **conflates two sub-modes** (flat-conjunction vs recognizer-not-reducing) — see C1/C2. Its site list (229/275/302/334/361) is off-by-one from the actual `obtain` lines (230/276/303/335/362) and **omits the entire downstream cluster**.
- Family 4: the `Proposition` case is already solved by `beqToEq`; `LawfulBEq.eq_of_beq` still works for `WorldIndex`. HOLDS / already applied.
- **Miss**: zero mention of C8 (`List.bind`), C9 (`List.mem_zip`), C12 (`mem_cons_self` arg-count), C13 (`Bool.or_eq_true.mp`), C7 (duplicate `imp`).

**Report 02 (`02_refactor-strategy.md`) — accurate on `modalStepBranch` structure, but its load-bearing premise is REFUTED and its remedy is over-engineered for a drift repair.**
- Its case map (lines 57-73), the 10 `hnewBs` site list, the `hInv`-only-in-boxNeg observation, and the `beqToEq` reuse note are all **accurate and useful**.
- Its premise "~68 remaining errors ALL inside this one theorem" is **false** (≈15 errors are in 798-945).
- Its refactor (extract 10 `private lemma`s + rewrite the main skeleton, via a Phase-0 that introduces 10 deliberate `sorry`s) is a **large structural change** carrying real risk (the `hsf` boundary unification, boxNeg's local `let`s) and a zero-debt tension it itself flags. For *faithful drift repair* this is heavier than warranted: the actual distinct roots are few, mostly mechanical, and — crucially — the `lake build` log already exposes the goal/term shapes needed (228, 276, 870, 900, 925) **without** the `lean_goal` calls that caused the overflow. **The catch-22 the refactor solves is largely dissolved by driving the repair from build output instead of `lean_goal`.**

### 4. Why Three Agents Overflowed — and the Cheaper Technique

The overflow trap is using `lean_goal` *immediately after* the giant `simp [tryAllPropRules,…] at hsf` inside `modalStepBranch`, which returns the full ~13-hypothesis context. **Avoid it**: (a) for `unsolved goals`/`cases failed` sites the `lake build` log already prints the relevant `hsf`/goal shape (verified: 228 prints the flat conjunction, 276 prints the un-reduced match); (b) for shape-discovery use `lean_multi_attempt` at the exact `obtain` line with candidate destructurings (`["obtain ⟨hnewBs,_,hnewAcc⟩ := hsf", "obtain ⟨rfl,_,rfl⟩ := hsf", "injection hsf"]`) rather than `lean_goal`; (c) read the file in ≤120-line slices. This is how this research inspected the whole file without overflow.

## Decisions

1. **Reject the full 10-sub-lemma refactor as the primary strategy.** Adopt in-place, build-log-driven, commit-per-cluster repair. Keep extraction as a *targeted fallback for boxNeg (N1) only* if that single case's mid-proof context genuinely overflows during repair.
2. **Fix order is dictated by cascade structure, not by report 02's phase list.** The keystone `List.bind` (C8) and the pervasive `mem_cons_self` (C12) should be fixed early because they unblock/declutter large downstream blocks and surface the *real* remaining errors.
3. **Treat C7 (duplicate `imp`) as a structural fix**, not drift — do it in the same chunk as the neg-branch cases.
4. **Zero-debt is achievable without intermediate `sorry`s** under in-place repair (no Phase-0 scaffolding needed), satisfying the task's zero-sorry/zero-axiom constraint more cleanly than report 02's scaffold.

## Recommendations — Chunked, Commit-by-Commit Repair Ordering

Each chunk ends with `lake build Cslib.Logics.Modal.Tableau.Soundness` and a commit. **Never** call `lean_diagnostic_messages`; use the build log + `lean_multi_attempt` for shape discovery; read in ≤120-line slices.

- **Chunk A — Downstream keystone + mechanical sweep (fast, high-leverage).**
  1. C8: `Soundness.lean:804` `branches.bind id` → `branches.flatMap id`.
  2. C12: replace all 14 `List.mem_cons_self _ _` → `List.mem_cons_self` (sites 233, 279, 311, 322, 341, 350, 368, 377, 433, 627, 651, 709, 732, 875).
  3. C13: `Soundness.lean:892` `rcases Bool.or_eq_true.mp hedge` → `rw [Bool.or_eq_true] at hedge; rcases hedge with h' | h'`.
  4. C15: `Soundness.lean:925` append `exact absurd hedge (by simp)` (or `simp at hedge`).
  Build. Expect C11/C14/C16 (HAppend/`hstep2`/`modalExpandBranches_closed_unsat`-unknown cascades) to largely clear once C8 de-poisons `ih`. Commit: `task 364: repair downstream Mathlib drift (List.bind, mem_cons_self, Bool.or_eq_true)`.

- **Chunk B — Zero-fuel zip block (C9/C10).** `Soundness.lean:820-828`: fix the `obtain` arity (2 binders), replace the `List.mem_zip` `rw` with a reconstruction (try `lean_multi_attempt` with `List.mem_iff_getElem`/`List.getElem_zip`/`List.mk_mem_zip_iff` candidates), re-derive 858. This is the messiest block — budget a probe here. Commit: `task 364: repair zero-fuel zip-membership block`.

- **Chunk C — boxPos (C1, 220-266).** Collapse the `split_ifs`/double-bullet at 227-231; use `simp only [Option.some.injEq, Prod.mk.injEq] at hsf` then flat `obtain ⟨rfl, _, rfl⟩ := hsf` (build already shows the flat shape). Verify the `simp only [Satisfies] at hpos` at 262 fires. Commit.

- **Chunk D — pos propositional cases (C2/C3): negPos 270-290, orPos 297-328, impPos 329-356, impPosGen 357-383.** For each, get `simp` to reduce `hsf` to a flat `RuleResult` conjunction (add recognizer-unfold/`decide` if a `match` persists — diagnose from the build's term dump), then flat `obtain`. These are near-identical; transcribe the working idiom across all four. Commit after the cluster (or in 1-2 sub-commits).

- **Chunk E — neg propositional cases (C5/C6 + C7): negNeg 620-638, orNeg 644-699, impNeg 700-723, impNegGen 724-746, and the duplicate-`imp` structural fix at 747.** Mirror of Chunk D plus the C7 arm rename/restructure. Commit.

- **Chunk F — boxNeg (C4 + Families 1/2/4, 396-616).** The long pole. Fix C4 obtain entry, then the in-case `mem_cons_self` (433, already done in Chunk A), `Bool.or_eq_true` simp (438, fine), `beqToEq` Family-4 sites (441/499/506/534/560), and Family-1 sign idioms (509-512, 553-557) using `cases h : … <;> simp_all [Sign.isPos]`. **Only if mid-case `lean_goal`/build context overflows**, extract `…_boxNeg_boxProps_sat` / `…_boxNeg_diaNegProps_sat` helpers per report 02 §5. Commit.

- **Chunk G — Zero-debt verification.** `lake build Cslib.Logics.Modal.Tableau.Soundness` clean; `lake build` (full); `lean_verify Cslib.Logic.Modal.Tableau.modalStepBranch_preserves_sat` and `…modalTableau_sound` show zero `sorry`/zero new axioms; `lake exe lint-style`; `lake exe checkInitImports`. Commit: `task 364: complete implementation`.

## Risks & Mitigations

- **Risk: C11/C14 are not pure cascades and persist after C8.** Mitigation: Chunk A ends with a build; if HAppend errors remain, they indicate a genuine mis-typed term at 869/882/899 — probe with `lean_multi_attempt` and adjust the `++`/`.map` chain. (Confidence the cascade hypothesis holds: HIGH but unverified.)
- **Risk: C9 zip block needs a lemma not yet identified.** Mitigation: `List.of_mem_zip` (reverse) + `List.mem_iff_getElem` are available; worst case, restructure to avoid proving zip-membership (the goal is only used to feed `findSome?_eq_none_iff`). Budget the most search time here.
- **Risk: Family-3 simp-reduction (C2/C5) resists.** Mitigation: the recognizers (`modalNegOf?`, `modalImpOf?`, `modalOrOf?`) are decidable pattern-matches; add `decide := true` to the simp config or unfold them explicitly. Re-read `Cslib/Logics/Modal/Tableau/Rules.lean` for their defs if needed.
- **Risk: boxNeg overflow.** Mitigation: the report-02 helper-extraction is a sound, pre-analyzed fallback — invoke it only for N1, only if needed.
- **Risk: statement preservation.** All public signatures (186-196, 798-812, 917-919) must stay byte-for-byte; C7's restructuring touches only the `cases` arm internals, not the statement. Verify with `git diff` that no theorem type changed.

## Appendix — Key Coordinates & Commands

- **Build log** (full, 1607 lines, 68 errors): regenerate with `lake build Cslib.Logics.Modal.Tableau.Soundness 2>&1`. Distinct error lines: 228, 229, 276, 304, 336, 363, 403, 625, 650, 706, 730, 747, 804, 822, 823, 828, 858, 869, 870, 875(×2), 882, 892(×2), 896, 899, 900, 925, 935.
- **`mem_cons_self _ _` sites (14)**: 233, 279, 311, 322, 341, 350, 368, 377, 433, 627, 651, 709, 732, 875.
- **`hnewBs` obtain sites (10)**: pos 230, 276, 303, 335, 362; neg 403, 625, 650, 706, 730.
- **Verified lemma modules**: `List.flatMap` (Init.Prelude), `List.mem_cons_self` (Init.Data.List.Lemmas), `List.of_mem_zip` (Init.Data.List.Zip), `List.mem_iff_get` (Init.Data.List.Lemmas), `Bool.or_eq_true` (Init.SimpLemmas).
- **Reuse (in-file, no new abstractions)**: `Proposition.beqToEq` (78), `branchSatisfiable` (63), `accFreshInv` (164), `accFreshInv_empty` (171), `modalClosed_unsat` (100); `Sign.isNeg_eq_not_isPos` (Sign.lean:87); `modalNextWorld_gt` (Branch.lean:104).

## Adversarial Self-Verification

I re-challenged every claim:
- **"Errors are downstream, not all in `modalStepBranch`"** — verified directly from `lake build` (errors at 804-935 are outside theorem boundary 787). Not an inference; ground truth. HIGH.
- **`List.bind` removed / `List.flatMap` is the replacement** — loogle confirms `List.flatMap` exists and `List.bind` returns nothing. HIGH.
- **`List.mem_cons_self` arg-count change** — loogle shows all-implicit signature; build error "Function expected" at the `_ _` application corroborates. HIGH.
- **`List.mem_zip` removed** — loogle "no results"; `List.of_mem_zip` is the only survivor and is the wrong direction. HIGH for removal; the exact replacement is the one place I could NOT fully verify a drop-in — flagged MEDIUM (C9).
- **`Bool.or_eq_true` is Eq not Iff** — loogle shows `((a||b)=true) = (…)`; `.mp` on an `Eq` is invalid. HIGH.
- **Flat-vs-nested conjunction is the C1/C3 cause** — verified for boxPos from the build's explicit `hsf` dump at 228 (right-associated `A ∧ B ∧ C`); for orPos/impPos (C3) it is a strong inference from the identical code pattern, not a direct dump — flagged HIGH for boxPos, MEDIUM-HIGH for the C3 siblings.
- **C2/C5 (recognizer-not-reducing)** — verified the *root* (build dumps the un-reduced `match`/`if` term at 276); the *fix* (strengthen simp set) is MEDIUM (depends on which lemma/config makes the recognizer compute).
- **C10/C11/C14/C16 are cascades** — C16 verified (name-not-registered); C11/C14/C10 are reasoned cascades from C8, explicitly flagged UNVERIFIED pending the Chunk-A rebuild. I did NOT overstate these as fixed.
- **Lemmas the prior reports name all exist** — verified by grep in `Basic.lean`/`Sign.lean`; corrected the one false prior claim (`Sign.isPos` characterization lemma does exist).
- **Could the refactor still be needed?** Challenged my own "over-engineered" verdict: the only genuine overflow risk is mid-`boxNeg`, for which I retained report 02's extraction as a scoped fallback rather than discarding it. The recommendation is therefore not a blanket rejection but a re-scoping.

Recommendations modified after verification: (1) elevated `List.bind`/line 804 to the **keystone first fix** (prior reports never mentioned it); (2) split Family-3 into two sub-modes with distinct idioms; (3) demoted the 10-sub-lemma refactor from "recommended" (report 02) to "boxNeg-only fallback"; (4) added the 14× `mem_cons_self` mechanical sweep as an early chunk. No Tier-1 BibKey citations apply (this is toolchain-drift repair against the Lean/Mathlib API, not a published-paper transcription); `references.bib` was therefore not consulted for citation grounding — reference grounding tier is effectively **Tier 3 (implementation/API-backed)**, grounded in verified lemma signatures and the live build.
