# Research Report: Reconcile Stale [BLOCKED] Docstrings in the Generic Tableau Driver

**Task**: 532 (cslib, docstring-only cleanup)
**Scope**: Sweep `GenericDriver.lean`, `Saturation.lean`, `FrameCompleteness.lean`,
`CompletenessLoop.lean` for docstrings that still narrate the now-delivered generic tableau
driver and the T / S5 / 5 (Euclidean) / KB5 decidability results as blocked or pending. Propose
corrections anchored to durable references (declaration names, file/section anchors), never task
numbers. No proof changes.

---

## Ground Truth: What Is Actually Live

Verified by `grep` + `Read` of the source (all in
`Cslib/Logics/Modal/Tableau/`):

| Decision instance | Location | Backing decision theorem |
|-------------------|----------|--------------------------|
| `instDecidableKValid` | `CompletenessLoop.lean:2295` | `modalTableau_decides` |
| `instDecidableTValid` | `FrameCompleteness.lean:1316` | `tValid_decides` (:1303) |
| `instDecidableBValid` | `FrameCompleteness.lean:1931` | `bValid_decides` |
| `instDecidableS5Valid` | `FrameCompleteness.lean:2427` | `s5Valid_decides` (:2416) |
| `instDecidableFiveValid` | `FrameCompleteness.lean:3218` | `fiveValid_decides` |
| `instDecidableKb5Valid` | `FrameCompleteness.lean:4314` | `kb5Valid_decides` |

**Crucially**, a *generic, frame-relativized soundness lift* now exists in
`FrameSoundness.lean` — the exact abstraction the stale `GenericDriver.lean` header says does
not exist:

- `frameValid` / `branchSatisfiableIn` (`FrameSoundness.lean:83` / `:110`) — the `FC`-parametric
  generalizations of `kValid` and `branchSatisfiable`.
- `modalStepBranchGen_preserves_satIn` (`:195`) — generic version of
  `SoundnessStep.lean`'s `modalStepBranch_preserves_sat`, taking raw
  `hAgree`/`hBoxPos`/`hDiaNeg` hypotheses rather than a hard-coded `modalApplyOne`.
- `modalExpandBranchesGen_closed_unsatIn` (`:731`) — the generic `(apply, spec)`-parametric
  fuel-induction soundness argument (the `_gen` form the old docstring claims "does not exist").
- `modalTableau_sound_frame` (`:909`) — K soundness re-derived through the generic vocabulary,
  confirming the K arms port unchanged.

`tValid_decides` (`FrameCompleteness.lean:1303`) combines `modalTableauT_sound` (delivered via
the `FrameSoundness.lean` generic chain) with `modalTableauT_complete`. So the T soundness gate
the header describes as an open ~500-line risk is closed.

---

## Findings by File

### 1. `GenericDriver.lean` — PRIMARY, must correct (lines 131-158)

The entire header section titled
`## Completeness Is Generic (task 510); Soundness Is Not Yet (task 503 Phase 6, blocked)`
is stale. Specific false claims:

- **Line 131 (heading)**: "Soundness Is Not Yet (task 503 Phase 6, blocked)". Soundness *is*
  generically lifted (`FrameSoundness.lean`).
- **Line 145**: "**Soundness has no such generic lift yet.**" — contradicted by
  `modalExpandBranchesGen_closed_unsatIn` / `modalStepBranchGen_preserves_satIn`.
- **Line 148**: "no `_gen`/`(apply, spec)` form exists" — `modalExpandBranchesGen_closed_unsatIn`
  is exactly that form.
- **Lines 148-149**: "Task 503 Phase 6 (`Decidable (tValid φ)`) is **[BLOCKED]** on this exact
  gap" — `instDecidableTValid` is live (`FrameCompleteness.lean:1316`).
- **Lines 150-158**: the predicted `branchSatisfiableIn FC`-generalized version, the "~500-line
  undertaking", and the "budget a soundness-lift phase … tasks 504 (S5) and 505 (B) will hit this
  same gap" forward-looking narrative are all now delivered
  (`branchSatisfiableIn` exists; S5 and B decidability instances are live).

The completeness paragraph (lines 133-143) remains **factually accurate** — the generic
completeness chain (`modalExpandBranchesGen_hintikka`, `CompletenessLoop.lean:1872`;
`modalApplyOneT_spec`, `TDriver.lean:847`) is real. Only its task-number citations and the
"Soundness Is Not Yet" framing are the problem.

**Proposed replacement** (docstring-only; durable anchors; the implementer should adapt wording
but preserve this factual content):

```
## Completeness and Soundness Are Both Generic Over `(apply, spec)`

The completeness-side Hintikka/saturation chain is fully generic over `(apply, spec)`:
`modalExpandBranchesGen_hintikka` (`CompletenessLoop.lean`) turns any
`RuleApplicationSpec apply` witness -- e.g. T's `modalApplyOneT_spec` (`TDriver.lean`) -- into a
Hintikka-set-producing top-loop lemma for free. The T-specific completeness work
(`hintikkaT_box_pos`/`hintikkaT_diamond_neg`, `modalTruthLemmaT`, `modalTableauT_complete`, all
in `FrameCompleteness.lean`) needed new content only at the two shapes where T's rule differs
from K's; the other two modal shapes reuse the free projection bridges
`hintikka_box_neg_gen`/`hintikka_diamond_pos_gen` (`Completeness.lean`).

The soundness side is likewise generic, via the frame-relativized chain in `FrameSoundness.lean`:
`branchSatisfiableIn FC` and `frameValid FC` generalize `branchSatisfiable`/`kValid` with an
explicit frame-condition predicate `FC`, and `modalStepBranchGen_preserves_satIn` /
`modalExpandBranchesGen_closed_unsatIn` are the `(apply, spec)`-parametric fuel-induction
soundness arguments (the ambient Kripke model is never replaced; only the world-assignment `f`
is pointwise redefined at the minting rules, so an `FC m.r` witness threads through unchanged).
`modalTableau_sound_frame` re-derives K soundness through this vocabulary to confirm the K arms
port unchanged. Each per-system tableau supplies its own `hAgree`/`hBoxPos`/`hDiaNeg` triple and
instantiates the generic chain -- see `modalTableauT_sound`, `modalTableauB_sound`,
`modalTableauS5_sound`, `modalTableauFive_sound` in `FrameCompleteness.lean`/`FrameSoundness.lean`.

Consequently the decision procedures are all delivered: `instDecidableTValid`,
`instDecidableBValid`, `instDecidableS5Valid`, `instDecidableFiveValid`, and
`instDecidableKb5Valid` (all in `FrameCompleteness.lean`), alongside K's `instDecidableKValid`
(`CompletenessLoop.lean`).
```

### 2. `Saturation.lean` — no change required

`grep` for `[blocked]`/`is blocked`/`not yet`/`remains blocked` returns nothing. The earlier
broad-pattern hits were legitimate: the bound-variable names `pending`/`pendingExp`/`pendingAccs`
(the processNext worklists) and the phrase "branch cannot pollute sibling branches" and
"`modalFuel` cannot itself reference `modalUniverse`". None are stale status narratives.

### 3. `CompletenessLoop.lean` — no change required

`grep` for blocked-status patterns returns nothing. The Phase-6 hits are legitimate section
headers for K completeness (`task 442 Phase 6, FINAL` — the delivered K result
`instDecidableKValid`), and the remaining hits are `pending*` worklist variable names and
"curried-`e` `Aux` cannot observe the advance". No stale status narrative. (Note: the file's
`task 442 Phase 6` citations are task-number references, but rewording them is out of this
task's docstring-BLOCKED-sweep scope — see Observation below.)

### 4. `FrameCompleteness.lean` — one clearly-stale item already fixed elsewhere; two
advisory-only phrasings

- **Line 1769-1770** ("This closes the loop the plan originally isolated as a `[BLOCKED]` Phase 9
  fallback: no fallback is needed since … the generalized frame-relativized soundness chain
  landed"): **accurate past-tense resolution note**, correctly points at `FrameSoundness.lean`.
  Not stale. No change needed (beyond the cross-cutting task-number observation below).

- **Lines 4415-4439** (the KB5 `modalApplyOneKb5'` scout/blocker note): ends with an explicit
  **"Resolved"** subsection stating KB5 completeness/decidability is delivered via
  `modalApplyOneKb5''` (`modalTableauKb5''_complete`/`kb5Valid_decides`/`instDecidableKb5Valid`)
  and explicitly says the retained note "[is] not stale, since `modalApplyOneKb5'` genuinely
  remains incomplete and frozen". Self-documenting and accurate. **Leave as-is.**

- **Lines 476 and 552** ("delivered here regardless of Phase 2's blocked status" /
  "independent of the blocked Phase 2 rule discharge"): **borderline / advisory**. These refer to
  the S5 *guarded universal-rule* Phase 2 termination obstruction (documented in
  `S5Simplification.lean`'s "Phase 2 Obstruction" section), which was never discharged head-on —
  S5 ultimately landed via the **witness-reuse rule** `modalApplyOneS5w`
  (`S5Simplification.lean:542`), which terminates at K's fuel and bypasses Phase 2. So "Phase 2
  blocked" is *historically accurate* for that specific rule route, and the extraction lemmas
  (`extractModelS5_equiv`, `extractModelS5_rightEuclidean`) genuinely are independent of it.
  However, because S5 / 5 decidability is now fully live (`instDecidableS5Valid`,
  `instDecidableFiveValid`), the bare word "blocked" risks misleading a reader into thinking S5 is
  unfinished. **Recommendation (optional):** soften to e.g. "the *bypassed* Phase 2 rule
  discharge (superseded by the witness-reuse rule `modalApplyOneS5w`, `S5Simplification.lean`)".
  This is a judgment call; it is not a false claim, so it is not mandatory for this task.

- **Lines 565-587** (the "5 / KB5 (Euclidean) Coverage … Status" section): already an explicitly
  **CORRECTED** note grounded in the frame-class separation probe. Accurate. Leave as-is.

---

## Cross-Cutting Observation (out of scope, flag only)

All four files pervasively cite task numbers inside docstrings (e.g. `task 510`, `task 503 Phase
6`, `Task 513`, `task 442 Phase 6`). Per `.claude/rules/no-task-references-in-deliverables.md`
these are technically rule violations (the files live outside `specs/**`). Stripping every such
citation is a much larger refactor than this task's stale-BLOCKED sweep and should **not** be
attempted here. The one hard constraint for this task: the **replacement** text proposed above
must introduce **zero** new task-number citations (it uses only declaration names and file
anchors). A dedicated follow-up task could sweep the residual task-number citations across the
`Tableau/` module if desired.

---

## Recommended Implementation Scope (docstring-only, zero proof changes)

1. **Required**: Replace `GenericDriver.lean` lines 131-158 with the corrected section above
   (retitle, drop "[BLOCKED]"/"not yet", anchor to `FrameSoundness.lean` generics and the live
   `instDecidable*Valid` instances; no task numbers).
2. **Optional / advisory**: Soften `FrameCompleteness.lean` lines 476 and 552 to name the
   witness-reuse bypass (`modalApplyOneS5w`) instead of the bare word "blocked".
3. **No change**: `Saturation.lean`, `CompletenessLoop.lean`, and `FrameCompleteness.lean` lines
   1769-1770 / 565-587 / 4415-4439.

**Verification after edits**: `lake build Cslib.Logics.Modal.Tableau.GenericDriver` (and
`…FrameCompleteness` if lines 476/552 are touched). Docstring-only edits cannot change proof
obligations; the build is a formatting/parse sanity check only. No `sorry`, no axioms, no
proof-term changes — fully compatible with the zero-debt gate.

## Reuse-First Note

No new definitions or abstractions are recommended. The correction *removes* a docstring that
incorrectly claims a needed abstraction is missing — the abstraction (`FrameSoundness.lean`'s
generic soundness chain) already exists and is the durable anchor the corrected text points to.
