# Research Report: Propositional Tableau Completeness Ground Truth and the TFAE Fold

**Task**: 606 — Discharge or restate the four propositional tableau completeness theorems and
verify the TFAE fold
**Session**: sess_1786375467_9fbdb7
**Date**: 2026-08-10
**Agent**: cslib-research-agent

---

## Executive Summary

**All four DP sites (DP-3, DP-4, DP-5, DP-6) are already discharged, sorry-free, and
machine-verified axiom-clean.** The predecessor tasks (603, 604, 605, 609) landed real proofs,
not negative results. `lake build` is green (exit 0, 3325 jobs, zero errors). Scope items (a)
"discharge each sorry" and (b) "repair every call site" are **complete and require no work**.

Two items of genuine residual work remain:

1. **Scope item (c) — stale annotations.** `Scheme.lean` is now *internally contradictory*: its
   frame-adequacy table (`:9552-9556`) records the post-repair state correctly ("augmented,
   post-repair | holds | **holds**"), while ~8 other annotation blocks in the same file still
   assert, in the present tense, that the augmented frame is REFUTED for positive persistence,
   that `truthLemma`'s T-imp case "stays `sorry`", that `openBranch_countermodel` has a
   "surviving existential", and — most severely — that reconciling the two conjuncts over one
   uniform `edges` is "**KNOWN IMPOSSIBLE** on the algorithm's current output" (`:9682`). That
   last claim sits 20 lines below a sorry-free proof that does exactly what it declares
   impossible.

2. **The TFAE fold — not yet done, and feasible.** `ProofSystemEquivalence.lean` contains **no
   tableau node at all**. Its three TFAEs are Hilbert/ND/SequentCalculus only. The task's HARD
   CONSTRAINT ("must still be strong enough to fold the tableau nodes into
   `cplProofSystemsTfae` / `iplProofSystemsTfae` / `mplProofSystemsTfae`") is therefore
   currently *untested* rather than satisfied. **This report machine-verifies that the fold
   type-checks** — a 6-probe scratch file compiled with `lake env lean`, exit 0, zero errors.

**Recommended disposition**: this task narrows to (c) annotation close-out plus landing the
verified TFAE fold. Zero new sorries and zero new axioms are achievable; no restatement of any
theorem is needed, so the "laundering a sorry via a weakened statement" hazard does not arise.

---

## 1. Ground Truth: The Four DP Sites

Line numbers in the task description are stale, as warned. Current state:

| Site | Declaration | Current location | Sorry? | Axiom profile |
|---|---|---|---|---|
| DP-3 | `intuitionisticTableau_complete` | `Tableau/Intuitionistic/Completeness.lean:177` | **none** | `{propext, Classical.choice, Quot.sound}` |
| DP-4 | `minimalTableau_complete` | `Tableau/Minimal/Completeness.lean:169` | **none** | `{propext, Classical.choice, Quot.sound}` |
| DP-5 | `truthLemma` | `Tableau/Intuitionistic/Scheme.lean:964` | **none** | `{propext, Classical.choice, Quot.sound}` |
| DP-6 | `openBranch_countermodel` | `Tableau/Intuitionistic/Scheme.lean:9586` | **none** | `{propext, Classical.choice, Quot.sound}` |

Axiom profiles obtained via `lean_verify` on fully-qualified names
(`Cslib.Logic.PL.<name>`); all four returned `{"axioms":["propext","Classical.choice",
"Quot.sound"],"warnings":[]}` — **no `sorryAx`**.

Textual confirmation: `grep -n '\bsorry\b'` across the three Lean files in scope returns only
prose occurrences inside docstrings (`Completeness.lean:40,43`; `Minimal/Completeness.lean:43,49`;
`Scheme.lean:800,7237`). There is no `set_option warn.sorry false` in any of the three files, and
no `sorry` tactic occurrence. `ProofSystemEquivalence.lean` has zero occurrences of the string.

**Build state**: `lake build` completed successfully, exit code 0, 3325 jobs. The only warnings
anywhere near this subsystem are two `linter.unusedDecidableInType` notices on
`ivalid_universe_invariant` (`Intuitionistic/DecisionProcedure.lean:159`) and
`mvalid_universe_invariant` (`Minimal/DecisionProcedure.lean:173`), both suggesting the
`[DecidableEq Atom]` hypothesis is unused. These are pre-existing, unrelated to this task's
scope, and cosmetic.

### 1.1 DP-3's proof and the in-source prohibition

The task description carries an explicit prohibition: do NOT discharge DP-3 with
`exact h Nat (intExtractValuation _b) _huc 0`. The landed proof is:

```lean
theorem intuitionisticTableau_complete (φ : Proposition Atom)
    (h : IValid.{_, 0} φ) : intuitionisticTableau φ = .closed := by
  apply tableau_complete intScheme
  intro edges _b _huc _hbuc
  exact @h Nat (intAccessPreorder edges) (intExtractValuation _b) _huc 0
```

This is the prohibited *shape*, but **not the prohibited act**, and the distinction is real
rather than a rationalization:

- The prohibition's stated ground was that the discharge "launders an undischarged conjunct
  through the file without resolving it". `_huc` is bound by `tableau_complete`'s `hvalid`
  premise (`Scheme.lean:9814-9820`), which is *supplied by* `openBranch_countermodel`
  (`Scheme.lean:9828`: `obtain ⟨edges, huc, hbuc, hcm⟩ := openBranch_countermodel S φ b hresult`).
- `openBranch_countermodel` is sorry-free and axiom-clean (verified above). Its conjunct 1 is
  proved at `Scheme.lean:9645-9660` by instantiating `hpersAug` at `χ := .atom p` and peeling
  the `ReflTransGen` chain; conjunct 2 at `:9661-9665` via `IntMinScheme.modelBot_uc` at
  `χ := HasBot.bot`.
- Therefore `_huc` is a genuinely proved fact, not an assumed one. There is no undischarged
  conjunct anywhere in the chain.

The docstring at `Completeness.lean:170-173` already records this reasoning explicitly ("the
prohibition this docstring used to record no longer applies"). **Verdict: the prohibition was
conditional on the conjunct being open; the condition no longer holds, and the discharge is
legitimate.** No action needed at DP-3.

### 1.2 What each predecessor actually landed

- **603**: `openBranch_rawEdges_upward_closed` (`Scheme.lean:9689`) — χ-general raw-edge
  upward closure — plus `openBranch_rawEdges_both_upward_closed` (`:9758`). Note these are now
  *unused by* `openBranch_countermodel`, which routes through the augmented frame instead.
- **604**: DP-5 discharged via the explicit `hpers` hypothesis on `truthLemma`
  (`Scheme.lean:968`), plus the frame-adequacy table.
- **605**: `minBranchBotForces` upward closure at the bot shape (now subsumed by the
  `modelBot_uc` field route).
- **609**: the decisive work — `intFImpReuseWitnessAnc?` loop-back re-validation, giving
  `hpersAug` (the 11th conjunct of `intExpandBranches_openBranch_sat`, `Scheme.lean:8266`), which
  is what makes the AUGMENTED frame carry positive persistence and `IFimpAccess`
  *simultaneously*. This is the fact that closed DP-6 and, through it, DP-3 and DP-4.

---

## 2. The TFAE Fold — Machine-Verified Feasible, Not Yet Landed

### 2.1 Current state of `ProofSystemEquivalence.lean`

The file (159 lines) declares six TFAE theorems plus one legacy iff. **None of them mentions a
tableau.** Each is a three-node Hilbert / ND / SequentCalculus equivalence:

| Theorem | Line | Node 1 | Node 2 | Node 3 |
|---|---|---|---|---|
| `cplProofSystemsTfae` | 58 | `Deriv PropositionalAxiom Γ.toList φ` | ND | `Nonempty (LKProof …)` |
| `cplProofSystemsTfaeClosed` | 72 | `Derivable PropositionalAxiom φ` | ND at `∅` | LK at `∅` |
| `iplProofSystemsTfae` | 90 | `Deriv IntPropAxiom Γ.toList φ` | ND | `Nonempty (LJProof …)` |
| `iplProofSystemsTfaeClosed` | 104 | `Derivable IntPropAxiom φ` | ND at `∅` | LJ at `∅` |
| `mplProofSystemsTfae` | 123 | `Deriv MinPropAxiom Γ.toList φ` | ND | `Nonempty (SeqProofMinimal …)` |
| `mplProofSystemsTfaeClosed` | 137 | `Derivable MinPropAxiom φ` | ND at `∅` | LM at `∅` |

The file's imports are the three SequentCalculus completeness modules plus `Mathlib.Data.List.TFAE`
and `Mathlib.Tactic.TFAE`. No tableau module is imported.

**The fold belongs in the three `…Closed` variants only.** The context-based variants quantify
over an arbitrary `Γ : Ctx Atom`; the tableau decision procedures are closed-formula procedures
(`intuitionisticTableau φ`, no context argument), so there is no tableau node to add to the
context-based statements.

### 2.2 The three bridges that make the fold work

All three already exist and are sorry-free:

| Logic | Derivable ↔ validity | Validity ↔ tableau | Universe reconciliation |
|---|---|---|---|
| CPL | `prop_completeness_iff_tautology` (`Metalogic/StrongCompleteness.lean:559`): `Tautology φ ↔ Derivable PropositionalAxiom φ` | `classicalTableau_decides` (`Tableau/Classical/DecisionProcedure.lean:68`) | none needed |
| IPL | `int_soundness_completeness` (`Metalogic/IntStrongCompleteness.lean:349`): `IValid.{u,u} φ ↔ Derivable IntPropAxiom φ` | `intuitionisticTableau_decides` (`Tableau/Intuitionistic/DecisionProcedure.lean:97`): `… = .closed ↔ IValid.{_,0} φ` | `ivalid_universe_invariant` (`…/DecisionProcedure.lean:165`) |
| MPL | `min_soundness_completeness` (`Metalogic/MinStrongCompleteness.lean:346`) | `minimalTableau_decides` (`Tableau/Minimal/DecisionProcedure.lean:113`) | `mvalid_universe_invariant` (`…/DecisionProcedure.lean:179`) |

The universe reconciliation step is load-bearing for IPL and MPL: the `Derivable ↔ validity`
bridges are stated at `IValid.{u,u}` / `MValid.{u,u}` while the tableau decision theorems are
pinned to `.{_,0}` (because the countermodel frame is `Nat : Type 0`). This is exactly the pin
the DP-3/DP-4 docstrings describe, and `ivalid_universe_invariant` / `mvalid_universe_invariant`
are precisely the bridges built to make it cost nothing.

### 2.3 Machine verification (exit 0)

A 6-probe scratch file was compiled with `lake env lean`. **Result: exit code 0, zero errors,
zero warnings.** Preserved at
`/tmp/claude-1000/-home-benjamin-Projects-cslib/2b7a4a92-9db5-490b-8511-e9e6eb44721a/scratchpad/tfae_probe.lean`
(deliberately kept out of the repo tree; the implementer should reuse it, not re-derive it).

Probes 1-3: the bare bridges. Probes 4-6: the four-node TFAE folds. The IPL fold, verbatim as
verified:

```lean
example (φ : PL.Proposition Atom) :
    [Derivable IntPropAxiom φ,
     DerivableIn (AxiomTheory (@IntPropAxiom Atom) : Theory Atom) ((∅ : Ctx Atom) ⊢ φ),
     Nonempty (LJProof ((∅ : Ctx Atom) ⊢ φ)),
     intuitionisticTableau φ = .closed].TFAE := by
  have h := iplProofSystemsTfaeClosed (Atom := Atom) φ
  tfae_have 1 ↔ 2 := h.out 0 1
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 1 ↔ 4 := by
    exact int_soundness_completeness.symm.trans
      ((ivalid_universe_invariant φ).trans (intuitionisticTableau_decides φ).symm)
  tfae_finish
```

MPL is the exact analogue with `min_soundness_completeness` / `mvalid_universe_invariant` /
`minimalTableau_decides`. CPL is simpler — no universe step — and closes with
`rw [← prop_completeness_iff_tautology, ← classicalTableau_decides]`.

### 2.4 Two implementation gotchas discovered empirically

Both were found by compiler feedback, not inferred, and will cost the implementer a cycle each
if not anticipated:

1. **`rw` cannot apply `ivalid_universe_invariant` / `mvalid_universe_invariant`.** The first
   attempt used `rw [ivalid_universe_invariant]` and failed with
   `Did not find an occurrence of the pattern IValid ?φ in the target expression IValid φ ↔ …`.
   The lemma is `IValid.{_, v} φ ↔ IValid.{_, 0} φ`; `rw` cannot solve for the universe level
   `v`. **Use term-mode `Iff.trans` composition instead**, as shown above. The CPL case has no
   universe parameter and `rw` works there.

2. **`[Hashable Atom]` is required.** `intuitionisticTableau` / `minimalTableau` /
   `classicalTableau` all need `[Hashable Atom]`, but `ProofSystemEquivalence.lean`'s
   `variable` line (`:47`) declares only `{Atom : Type*} [DecidableEq Atom]`.

   **Recommendation: add the tableau folds as NEW theorems in a new section carrying a local
   `variable [Hashable Atom]`, rather than adding a fourth node to the existing six theorems.**
   Rationale: adding `[Hashable Atom]` to `iplProofSystemsTfaeClosed` etc. changes their public
   signatures. That is a strictly larger change with no compensating benefit, and it would
   impose a `Hashable` constraint on the pure proof-theoretic equivalences, which have no
   business requiring it.

   Note in passing: **there are currently zero consumers of any TFAE theorem** anywhere in
   `Cslib/` or `CslibTests/` (only `Cslib.lean:566` imports the module). So even the invasive
   option would break nothing — but the new-theorem route is still the right call on design
   grounds.

3. **Import additions**: `ProofSystemEquivalence.lean` will need `public import` of the three
   `Tableau/*/DecisionProcedure` modules and `Metalogic/StrongCompleteness`. No cycle risk —
   nothing in `Cslib/` imports `ProofSystemEquivalence`. Be aware the build cost of this module
   rises substantially (it pulls in `Scheme.lean`, 9833 lines). After the change, run
   `lake exe mk_all --module` is unnecessary (no new file) but
   `lake shake --add-public --keep-implied --keep-prefix` should be checked.

---

## 3. Scope Item (c): The Stale Annotation Inventory

This is the bulk of the remaining work. The severity ordering below is deliberate.

### 3.1 The central contradiction (SEVERE — fix first)

**`Scheme.lean:9667-9688`**, the docstring of `openBranch_rawEdges_upward_closed`. Current text
asserts, in the present tense:

> "This lemma is decoupled from `openBranch_countermodel`'s own `sorry` above, which commits to
> no `edges` witness at all … Reconciling the two conjuncts over one uniform `edges` is now
> **KNOWN IMPOSSIBLE** on the algorithm's current output, not merely undone: `rawEdges` supports
> positive persistence but is REFUTED for `IFimpAccess` …, while the augmented frame
> `openBranch_countermodel` used to commit to supports `IFimpAccess` but is REFUTED for positive
> persistence — neither edge list the algorithm currently produces carries both. Closing this gap
> is calculus-level work on `intFImpReuseWitnessAnc?` (`Expansion.lean`), outside this file's
> scope."

Every clause of this is now false:
- `openBranch_countermodel` (`:9586`) has no `sorry` and **does** commit to an `edges` witness
  (the augmented one, `:9604`).
- The "KNOWN IMPOSSIBLE" reconciliation is performed 80 lines above, at `:9644-9665`.
- The frame-adequacy table at `:9552-9556` — in the *same file* — already records
  "augmented (`augSets`), post-repair | holds | **holds** (`hpersAug`, this file)".
- The calculus-level work on `intFImpReuseWitnessAnc?` named as "outside this file's scope"
  is exactly what task 609 landed.

**Additional consideration for the implementer**: `openBranch_rawEdges_upward_closed` and
`openBranch_rawEdges_both_upward_closed` (`:9689`, `:9758`) are now *unused* — nothing calls
them, since `openBranch_countermodel` routes through `hpersAug` at the augmented frame instead.
They should be retained (they are the durable record of the raw-frame route and cost nothing),
but their docstrings must say so plainly rather than claiming to be the live route around an
impossibility.

### 3.2 Present-tense "REFUTED at the augmented frame" claims (SEVERE — systematic)

`CslibTests/BetaSplitRefutation.lean`'s own module header now states:

> "**Post-repair status**: the beta-priority repair (`intStepBranchPrio`, `Expansion.lean`)
> closes the defect this file documents. Every `#guard_msgs` assertion below is asserted against
> the REPAIRED calculus and passes — the persistence-violation field that used to read
> `some (2, 1, 2)` now reads `none` …"

So `BetaSplitRefutation.lean` refutes the **pre-repair** calculus only. Every in-source citation
of it as a *current* refutation is stale and must be re-tensed. Sites:

| Location | Stale claim |
|---|---|
| `Scheme.lean:796-800` | "the obstruction … is real only at the AUGMENTED frame, where `hpers` is itself REFUTED (`CslibTests/BetaSplitRefutation.lean`)" |
| `Scheme.lean:849-851` | "does **not** discharge the `sorry` immediately below (DP-5's augmented-frame instantiation), which genuinely depends on the AUGMENTED-frame positive-formula persistence invariant and is refuted at `phiRef1`" |
| `Scheme.lean:1000-1008` | in-proof comment: "`hpers` is REFUTED at the AUGMENTED frame … refuted over the augmented frame" |
| `Scheme.lean:7226-7233` | `IPosPersistRaw` docstring: "that augmented-edge route is now known-refuted rather than pending" |
| `Scheme.lean:9682-9688` | see 3.1 above |
| `Expansion.lean:525-545` | "**Recorded limitation: a FRAME-CONSTRUCTION defect** … the loop-back edge `(x, w)` it records is **never re-validated** afterwards … This is machine-verified, not hypothetical" — this is the pre-repair description of the very thing 609 repaired |

Per the task's stated precedent (`intExpandBranches_openBranch_sat`'s counter-instance record
survives near `:8256` / `:8475` as the durable explanation of why the R1 hypotheses exist), the
correct treatment is **re-tense and mark historical, not delete**. The `phiRef1` counterexample
is exactly why `hpersAug` and the loop-back re-validation exist; deleting the record would
destroy the explanation of the hypotheses' provenance.

### 3.3 Stale "still open / still sorry" claims (MODERATE)

| Location | Stale claim | Correct wording |
|---|---|---|
| `Scheme.lean:742-783` | "**Blocker (documented, not a `sorry`…)** … which is exactly the `sorry` at `Completeness.lean:113`/`Minimal/Completeness.lean:110`" + a "Recommendation for continuation" | Both cited sorries no longer exist; both line refs are stale. Monotonicity is now supplied by `hpersAug`. |
| `Scheme.lean:819` | "**Gap 1 (fuel entanglement) is UNCHANGED and remains the sole blocker.**" | Partially corrected at `:840` ("this claim is STALE") but the heading still reads as current. |
| `Scheme.lean:864-866` | "The case nonetheless **stays `sorry`** … Gap 1 above, which is not yet established." | DP-5 is discharged. |
| `Scheme.lean:908-941` | "**Recommendation for continuation**" + "The augmented-frame gap this paragraph names is real and **still open**, but it now blocks a DIFFERENT goal: `openBranch_countermodel`'s own **surviving existential**" | That existential is discharged. |
| `Scheme.lean:945` | `truthLemma` docstring opens "Parametric truth lemma (**the single deferred completeness obligation**)." | It is deferred nothing. |
| `Scheme.lean:3226-3251` | "the fourth … carries the **DP-2 strategic sorry** for `hNW`'s OWN forward preservation … this lemma's proof is deferred … Follow-up: DP-2, see the plan's Planned Strategic Sorries table." | No DP-2 sorry exists; the file is sorry-free. |
| `Scheme.lean:9578-9581` | "Re-validating it is what lets the augmented frame carry positive persistence … and **closing this lemma's `sorry`**." | Present-tense residue; should read "closed". |
| `Scheme.lean:9807-9809` | "This theorem is sorry-free **given** `openBranch_countermodel S`; **the deferred obligation** … now lives entirely inside `openBranch_countermodel`" | Conditional framing; the obligation is discharged, so it is sorry-free outright. |
| `Completeness.lean:88-89` | "**The single deferred completeness obligation** now lives in `openBranch_countermodel`" | Same phrase, same staleness. |
| `Minimal/Completeness.lean:99-100` | identical phrase | same |

### 3.4 Adjacent files, out of the four-file scope but carrying the same stale claim (MINOR)

These are call sites of the annotation rather than of the theorem. Flagged for the planner to
decide in/out of scope:

- `Metalogic/IntDecidability.lean:321-325`: "the payoff is low while `openBranch_countermodel`
  … — which `truthLemma` alone does not discharge — **remains open**."
- `Metalogic/MinDecidability.lean:289-293`: identical claim.
- `Tableau/Minimal/DecisionProcedure.lean:56-59`: "closing what used to be this dependency
  chain's one remaining declaration-level sorry" — already correctly past-tense; **no change
  needed**, listed only to record that it was checked.
- `Tableau/Intuitionistic/Expansion.lean:525-545`: see 3.2.

### 3.5 Stale internal line references (MINOR, but worth a sweep)

The annotations cite line numbers that have drifted. Confirmed examples:
- `Scheme.lean:9555` frame-adequacy table cites `IFimpAccess` "holds (`:6924`)" — line 6924 is
  now inside `intuitionisticTableau_sound`.
- `Scheme.lean:747` cites "`sorry` at `Completeness.lean:113`/`Minimal/Completeness.lean:110`" —
  both now point at ordinary proved code.
- `Scheme.lean:799` cites "`IPosPersistRaw`/`IWorldsPlanted`, `:6782`/`:3568`" — `IPosPersistRaw`
  is at `:7239`.
- `IntDecidability.lean:312` and `MinDecidability.lean:277` cite
  "`Tableau/Intuitionistic/Scheme.lean:234`" for `truthLemma` — it is at `:964`.
- The task description's own references (`:154`, `:150`, `:693`, `:7891`, `:6815`) are all stale.

**Recommendation**: prefer declaration names over line numbers when rewriting. Line references
in a 9833-line file that is still under active development will drift again; the four DP sites
have already drifted twice.

---

## 4. Reuse Check (CSLib reuse-first)

No new abstraction is needed anywhere in this task. Confirmed by search:

- The TFAE fold reuses `Mathlib.Tactic.TFAE`'s `tfae_have` / `tfae_finish` and `List.TFAE.out`,
  exactly as the six existing theorems do. No new tactic or combinator.
- All three `Derivable ↔ validity` bridges and all three `validity ↔ tableau` bridges already
  exist as named theorems (table in §2.2). Nothing new to state.
- `ivalid_universe_invariant` / `mvalid_universe_invariant` already exist for precisely the
  universe reconciliation the fold needs — they were built for
  `instDecidableDerivableIntPropAxiom` / `instDecidableDerivableMinPropAxiom` and compose
  directly here.
- No new notation, no new typeclass, no new `Foundations/` abstraction.

The only new declarations are the three TFAE theorems themselves, which are pure compositions.

---

## 5. Zero-Debt Compliance

- **No sorry deferral is recommended anywhere in this report.** No sorry exists to defer.
- **No new axioms.** The fold composes existing theorems; the probe's axiom footprint is
  inherited from `{propext, Classical.choice, Quot.sound}`.
- **No restatement of any theorem is needed**, so the "laundering a sorry via a weakened
  statement" prohibition is not engaged. The four DP statements stand as landed.
- **No vacuous definitions.** The fold is machine-verified to type-check as stated.

---

## 6. Lint Prevention Notes for the Implementation Phase

- New TFAE theorems need docstrings (docBlame). Follow the existing pattern in the file:
  a `**Bold Title**` line, the numbered node list, then the composition rationale.
- Prop-valued: use `theorem`, matching the six siblings.
- Names: lowerCamelCase, no underscores — e.g. `iplProofSystemsWithTableauTfae`, matching
  `iplProofSystemsTfaeClosed`'s style. Avoid the `_` forms.
- Update the module docstring's `## Main Results` list (`:22-31`) and `## Dependencies` list
  (`:33-38`) to include the new theorems and the three bridge families — otherwise the module
  header becomes stale the moment the fold lands, which is precisely the failure mode this task
  exists to clean up.
- The two `linter.unusedDecidableInType` warnings on `ivalid_universe_invariant` /
  `mvalid_universe_invariant` are pre-existing and out of scope; do not "fix" them as a
  side-effect, since changing those signatures touches the `Decidable` instances.

---

## 7. Recommended Phase Decomposition

1. **Phase 1 — Land the TFAE fold.** Add imports + three theorems to
   `ProofSystemEquivalence.lean`, reusing the verified probe text verbatim. Update the module
   docstring. `lake build Cslib.Logics.Propositional.ProofSystemEquivalence`.
2. **Phase 2 — Fix the central contradiction.** Rewrite `Scheme.lean:9667-9688`
   (`openBranch_rawEdges_upward_closed`'s docstring), removing the "KNOWN IMPOSSIBLE" claim and
   recording the lemma's actual current status (retained raw-frame record, not the live route).
3. **Phase 3 — Re-tense the augmented-frame refutation claims** (§3.2), marking them historical
   / pre-repair rather than deleting them, per the preserve-the-counter-instance-record precedent.
4. **Phase 4 — Clear the "still open / still sorry" claims** (§3.3) in `Scheme.lean`,
   `Completeness.lean`, `Minimal/Completeness.lean`.
5. **Phase 5 — Adjacent files** (§3.4) and the stale-line-reference sweep (§3.5), if the planner
   scopes them in.
6. **Verification** — full `lake build`, plus `lake test` (the `CslibTests/` probe files carry
   `#guard_msgs` assertions that pin the algorithm's behaviour; they must still pass), plus
   `lake exe lint-style`.

Note that phases 2-5 are documentation-only and cannot break the build, so they can be
parallelized by file if the planner uses territory contracts. Phase 1 is the only phase with
proof content, and it is already machine-verified.

---

## 8. Open Questions for the User / Planner

1. **Should the tableau node be added to the context-based TFAEs as well?** This report
   recommends no — the tableau procedures are closed-formula only. If a context-based tableau
   node is wanted, that is new proof work (a deduction-theorem route), not a fold, and should be
   a separate task.
2. **Scope of §3.4 (adjacent files).** `IntDecidability.lean` / `MinDecidability.lean` /
   `Expansion.lean` are outside the four-file scope named in the task description but carry the
   same stale claim. Recommend including them, since leaving them makes the repo's account of
   its own state inconsistent again.
3. **Whether `openBranch_rawEdges_upward_closed` / `openBranch_rawEdges_both_upward_closed`
   should be retained.** This report recommends retention with corrected docstrings. They are
   dead code in the strict sense but constitute the durable record of the raw-frame route.
