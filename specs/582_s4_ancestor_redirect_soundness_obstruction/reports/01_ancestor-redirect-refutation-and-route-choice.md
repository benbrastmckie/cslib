# Research Report: `branchSatisfiableIn_s4FC_ancestor_redirect` — Obstruction Resolution

**Task**: 582 — resolve the repository's only unowned `sorry`
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
**Date**: 2026-08-06
**Status**: RESEARCHED
**Recommendation**: **Route (c) — DELETE**, with the finding relocated, not discarded.

---

## Headline Finding (new; supersedes the in-file docstring's framing)

**The lemma's statement is FALSE.** Not "unproven", not "unprovable from the available
hypothesis set" — refutable. I constructed an explicit three-world countermodel and
machine-checked the refutation against the live tree.

```
'RefuteAncestorRedirect.statement_is_false' depends on axioms: [propext, Quot.sound]
'RefuteAncestorRedirect.sat_before'         depends on axioms: [propext, Quot.sound]
'RefuteAncestorRedirect.not_sat_after'      depends on axioms: [propext]
```

No `sorryAx`. No `Classical.choice`. The probe file is preserved at
`/home/benjamin/Projects/cslib/specs/582_s4_ancestor_redirect_soundness_obstruction/scratch_refute_ancestor_redirect.lean`
and compiles clean under `lake env lean` (exit 0, zero diagnostics).

This single fact collapses the route decision: **route (a) is impossible**, because there is no
proof of a false statement to import from Massacci's deferred references or from anywhere else.

### The countermodel

Labels are `Nat`. Take `x = 0`, `src = 1`, `a = 2`.

| Item | Value |
|------|-------|
| `acc` | `⟨[(0,1), (2,1)]⟩` — edges `0 → 1` and `2 → 1` |
| `b` | `[ T(□p)@0 , F(p)@2 ]` |
| `hanc` | `acc.hasEdge 2 1 = true` ✓ (the edge `a → src`) |
| `hboxback` | holds **vacuously** — no `T(□ψ)@1` on the branch |
| `hdianeg` | holds **vacuously** — no `F(◇ψ)@1` on the branch |

`b` **is** S4-satisfiable at `acc`. Witness: `R i j := (j = i ∨ j = 1)` on `Nat`, with `p` true
exactly at `{0, 1}`, and `f = id`. `R` is reflexive and transitive, realizes both recorded edges
(every recorded edge has target `1`, and `R i 1` holds for all `i`), and `R`'s successor set of
`0` is exactly `{0,1}` where `p` holds — so `T(□p)@0` is satisfied — while `p` fails at `2`, so
`F(p)@2` is falsified. `R 1 2` is false, which is the point.

`b` is **not** S4-satisfiable at `acc.addEdge src a = acc.addEdge 1 2`, in *any* model. The edge
conjunct forces `m.r (f 0) (f 1)` and `m.r (f 1) (f 2)`; `IsTrans` forces `m.r (f 0) (f 2)`;
`T(□p)@0` then forces `p` at `f 2`; `F(p)@2` says `¬p` at `f 2`. Contradiction — with no appeal
to the choice of witness.

### Why this is a *simpler* obstruction than the docstring records

The module comment (`FrameSoundness.lean:1159-1188`) attributes the failure to the witness
model's **ambient, unconstrained** predecessors of `f src` — predecessors that need not lie on
any recorded spine, and that `hboxback`/`hdianeg` (which speak only about `src`) cannot control.
That diagnosis is correct as far as it goes, but the counterexample above needs nothing so
exotic: **`0 → 1` is a RECORDED `acc` edge.** The lemma already fails for an ordinary recorded
`acc`-ancestor of `src`.

The actual defect is structural and much more basic than the docstring suggests:

> `hboxback`/`hdianeg` constrain the box/diamond payload at `src` only. But in a transitive
> frame, adding `src → a` transmits box-positive content from **every `acc`-ancestor of `src`**
> down to `a`, not just from `src`. Nothing in the hypothesis set mentions those ancestors, so
> nothing prevents one of them carrying a `T(□ψ)` whose `ψ` the branch explicitly falsifies at
> `a`.

The hypothesis set is not merely *too weak to prove* the conclusion; it is too weak to make the
conclusion *true*. No amount of additional proof effort, imported machinery, or literature
archaeology changes that.

---

## 1. Consumer Audit (re-run live, 2026-08-06)

The task brief's audit is correct in substance and slightly wrong in detail.

```
$ grep -rn 'branchSatisfiableIn_s4FC_ancestor_redirect' --include='*.lean' Cslib/ CslibTests/
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1206   (docstring — quotes the audit command)
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1227   (the declaration itself)
Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5294   (docstring — cross-reference)
3 hits
```

**Confirmed: ZERO code consumers.** The `sorry` propagates into no other result.

Two corrections to the brief:

1. The brief places the third hit at `LoopChecking.lean:113`. It is **not** there — it is at
   `FrameSoundness.lean:5294`, inside the `accPinnedBy` module comment. (`LoopChecking.lean`
   around :113-115 discusses birth-key blocking and, per the task-566 report, once carried a
   *count* citation; the name itself does not appear in that file today.)
2. There is a **fourth**, non-`.lean` reference the brief does not mention:
   `Cslib/Logics/Modal/Tableau/README.md:66`, the subsystem sorry census.

Full deletion-impact surface is enumerated in §5.

## 2. The In-File Record: What Holds, What Is Superseded

Reading `FrameSoundness.lean:1159-1251`:

| Claim in the docstring | Verdict |
|---|---|
| Zero consumers; the `sorry` is a recorded obstruction, not load-bearing debt | **HOLDS** (§1) |
| Massacci (2000) Thm 8.1 is *stated and never proved*; App. B.2 proves only Thm 8.4; the paper defers to refs [7]/[20] | **HOLDS** — accepted as recorded, not re-derived (per the task's explicit instruction) |
| "Any further attempt to close this `sorry` by following that citation will find nothing to follow" | **HOLDS — and is now moot.** There is nothing to follow *and* nothing to prove |
| The obstruction is that no *standalone, driver-independent* hypothesis set can supply the needed content transfer | **UNDERSTATED.** The statement is false outright; a recorded `acc`-ancestor suffices to refute it |
| The `sorry` is "retained by explicit user decision" | **HOLDS** — this is the decision route (c) must reverse |

The Massacci finding and the refutation are consistent, and together they explain each other.
Massacci's Theorem 8.1 concerns blocking on a **π-completed** branch — i.e. a *saturated*
branch. The lemma here drops saturation entirely in pursuit of a driver-independent statement.
That is exactly the hypothesis whose absence the countermodel exploits: the branch
`[T(□p)@0, F(p)@2]` is nowhere near saturated (the 4-rule has not propagated `T(□p)` along
`0 → 1`, and nothing has propagated to `2`). So the citation was never going to close this
lemma even if Massacci *had* proved Theorem 8.1 — the two statements are about different things.

## 3. Dependency-Task Findings

### Task 553 — `s4_loop_guard_soundness_reachability_restriction` [COMPLETED]

**Decisive.** This task landed the successor route, **sorry-free**, and carried it to the
capstone `modalTableauS4KeyedOrdered_sound` establishing unweakened `s4Valid`. Its own summary
records: *"the single `FrameSoundness.lean:1251` standing user-decision sorry untouched"* — it
deliberately routed around this lemma rather than through it.

Two artifacts of that route matter here:

- **`branchSatisfiableIn_s4FC_addEdge_of_blocked`** (`FrameCompleteness.lean:4356). This has the
  **exact same conclusion shape** as the sorry'd lemma — `branchSatisfiableIn s4FC b (acc.addEdge
  src wBlock)` — and it is **proven**. It succeeds precisely because it takes
  `modalHintikkaSetS4 φ₀ b acc` as a hypothesis and builds the witness via
  `extractModelS4` + `modalTruthLemmaS4`. That construction *is* the model-graph argument
  Massacci defers to reference [20]. **The repository already has route (a)'s machinery, already
  applied, already sorry-free — under the hypotheses that make the conclusion true.**
- **`accPinnedBy` / `branchSatisfiablePinnedIn`** (`FrameSoundness.lean:5323`, `:5333`). Route
  (1)'s pinning device, which upper-bounds `m.r` on the branch's label image by
  `ReflTransGen acc`. Its own module comment explains exactly why the standalone lemma fails and
  the pinned one works: pinning *forces* an ambient predecessor of `f src` among known labels to
  be an `acc`-ancestor of `src`, "a set the tableau's own 4-rule has already propagated
  box-positive content to."

Crucially, `FrameSoundness.lean:5292-5295` already classifies this lemma as **dead**:

> "three prior soundness routes for this guard died precisely because the witness model's
> ambient predecessors of the redirect's source label were uncontrolled
> (`branchSatisfiableIn_s4FC_ancestor_redirect` above; ancestor-only blocking; the origin-edge
> revision)."

So the tree's own prose already names this lemma as a *retired* route, superseded by a landed
one. The task brief asks whether task 553's finding "informs whether route (b) has a target at
all". It does, and the answer is that the target is already occupied by proven code.

### Task 566 — `boneyard_creation_eligible_moves` [COMPLETED]

Established the carve-out this task must now dissolve. From its report §3.1:

> "It is genuinely zero-consumer … It is nevertheless **IMMOVABLE**, for exactly the reason the
> task states: it carries the one retained `sorry` in Modal/Tableau, which is an explicit user
> decision."

The carve-out rationale is *entirely* parasitic on the `sorry`'s existence. It cites two
mechanical confirmations, both of which are consequences of the retention, not independent
grounds: the `axiom-census-baseline.txt` row (which exists only because the declaration is
`sorryAx`-tainted) and the docstring's own retention note. **Remove the `sorry` and both
confirmations vanish with it.** Task 566 also independently confirms the "moving, never
deleting" disposition is right for *provenance-bearing* code — which is why §6 below relocates
the finding rather than dropping it.

### Tasks 567, 586 — vetting and duplicate adjudication [COMPLETED]

- **567** ran the full CI acceptance gate green across eleven blocking criteria and is the source
  of the current measured baseline. It also demonstrates the house standard: documentation
  figures are live-re-measured, and drifted numeric prose is a defect to be corrected.
- **586** is directly relevant precedent for route (c). It **deleted** a zero-consumer duplicate
  re-derivation (`modalSubfmls_self_mem_S5`), rerouted its call sites, and "reconciled three
  prose records the deletions falsified", with all CI gates at baseline. That is exactly the
  shape of the route (c) work, including the prose-reconciliation obligation.

## 4. Route Analysis

### Route (a) — Import the model-graph construction from Massacci's refs [7]/[20]

**VERDICT: IMPOSSIBLE. Eliminated on logical grounds, not cost grounds.**

The statement is refutable (§0). No construction proves it. Separately, even setting the
refutation aside, this route was already redundant: `extractModelS4` + `modalTruthLemmaS4` +
`branchSatisfiableIn_s4FC_addEdge_of_blocked` **already are** the model-graph route, landed and
sorry-free under a Hintikka hypothesis. Route (a) would be reimporting machinery the tree
already has, in order to prove a proposition that is false.

Cost: unbounded. Yield: zero. **Do not attempt.**

### Route (b) — Restate to something provable and still meaningful

**VERDICT: TECHNICALLY POSSIBLE, BUT PRODUCES A DUPLICATE. NOT RECOMMENDED.**

Because the statement is false, any restatement must *add* hypotheses (weakening the conclusion
is barred by the task's anti-vacuity constraint). What must be added is content that controls
box/diamond payload at the `acc`-ancestors of `src`. There are exactly three known ways to
supply that, and the tree already implements all three:

| Added hypothesis | Already-landed lemma | Location |
|---|---|---|
| `accPinnedBy` (pin `m.r` to `ReflTransGen acc`) | `branchSatisfiablePinnedIn_redirect_mechanical` | `FrameSoundness.lean:5356` |
| `modalHintikkaSetS4` (saturation) | `branchSatisfiableIn_s4FC_addEdge_of_blocked` | `FrameCompleteness.lean:4356` |
| `S4RedirectSoundInv` (ghost-edge quarantine) | the `S4RedirectSoundInv_*` family (14 results) | `FrameCompleteness.lean:5139+` |

So route (b)'s honest outcome is a fourth statement of a fact already proved three times, in a
file whose own comment already declares this route dead. That runs directly against the
duplicate-elimination discipline task 586 just enforced across this same subsystem, and it would
re-inflate the surface that task 566's Boneyard convention exists to shrink.

The one restatement that would *not* be a duplicate — keeping the driver-independence and adding
only a hypothesis about `src` — is precisely what the countermodel forbids.

Cost: moderate. Yield: negative (net new duplicate). **Not recommended.**

### Route (c) — Delete the lemma

**VERDICT: RECOMMENDED.**

- **Licensed**: zero code consumers (§1), independently confirmed by task 566's audit and
  re-confirmed live today. Nothing weakens.
- **Correct**: the declaration asserts a **false proposition**. A false statement retained in
  the tree behind a `sorry` is worse than debt — if anyone ever discharged that `sorry` by
  unsound means, or if a future refactor loosened it into a consumed position, it would be a
  soundness hazard. Deleting is the only disposition that removes the hazard.
- **Precedented**: task 586 deleted a zero-consumer declaration and reconciled the falsified
  prose, with CI at baseline throughout.
- **Unblocking**: it discharges the repository's only unowned `sorry`, brings Modal/Tableau to
  **0** sorries, and dissolves the task 566 carve-out that keeps a false statement in the tree
  indefinitely.

The retain-by-user-decision must be reversed, and the reversal is well-motivated: the decision
was made to preserve a *recorded obstruction*. The obstruction record is now strictly better
served by a refutation than by a `sorry` — see §6.

## 5. Deletion-Impact Surface (route (c) work list)

Verified live. Six touch points; none is a proof.

| # | File | What changes |
|---|---|---|
| 1 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:1159-1251` | Delete the section comment, the lemma docstring, and the lemma (incl. the sole `sorry` at :1251) |
| 2 | `Cslib/Logics/Modal/Tableau/FrameSoundness.lean:5294` | Cross-reference names the deleted lemma; rewrite (and see §6 — this is the relocation target) |
| 3 | `Cslib/Logics/Modal/Tableau/README.md:66-68` | Sorry census: "**1** in this subsystem" → **0**; "**28** code-position sorries repo-wide" → **27**; drop the "retained, user-decided, immovable obstruction" clause |
| 4 | `scripts/axiom-census-baseline.txt:40` | Remove the row `Cslib.Logic.Modal.Tableau.branchSatisfiableIn_s4FC_ancestor_redirect`. **Do not hand-edit** — the header says regenerate via `scripts/check-axiom-census.sh --update`. File goes 58 → 57 lines; the `sorryAx`-tainted ratchet goes 43 → 42 |
| 5 | `specs/ROADMAP.md:146` | "**28** code-position sorries repo-wide" → 27 (specs-tree; task-number citations permitted here) |
| 6 | Task 566's carve-out record | Record that carve-out 1's rationale no longer applies (per this task's definition of done) |

Measured baselines confirming the above, taken today:

```
FrameSoundness.lean code-position sorries : 1  (line 1251)
Repo-wide code-position sorries           : 28
axiom-census-baseline.txt rows            : 58  (Modal/Tableau rows: exactly 1)
```

`specs/TODO.md:183` also cites `sorries 28/28` and `sorryAx-tainted declarations 43/43` inside
another task's measured-state prose. That is a historical measurement record in the specs tree,
not a live ratchet — it should be left alone unless that task is itself re-run.

**Not in scope**: no proof, definition, or theorem statement elsewhere is altered. The
`accPinnedBy` / `S4RedirectSoundInv` / `branchSatisfiableIn_s4FC_addEdge_of_blocked` machinery is
untouched.

## 6. Preserve the Finding — Relocation, Not Erasure

Deleting the lemma must not delete the knowledge. Three facts are worth more than the `sorry`
ever was, and all three should survive:

1. **The statement is false**, with the explicit countermodel (`b = [T(□p)@0, F(p)@2]`,
   `acc = {0→1, 2→1}`, redirect `1→2`) — small enough to state inline in three lines.
2. **Why it is false**: transitive closure transmits box-positive payload from every
   `acc`-ancestor of `src`, and a hypothesis set mentioning only `src` cannot see them.
3. **The Massacci citation is a dead end**, and additionally a category error here: Thm 8.1
   concerns π-completed (saturated) branches, which is exactly the hypothesis this lemma drops.

The natural home is the `accPinnedBy` module comment at `FrameSoundness.lean:5280-5295`, which
*already* names this lemma as one of three dead routes and already explains the pinning fix. That
turns a scattered obstruction record into a single coherent narrative: here is why the naive
statement fails (with a countermodel), and here is the invariant that repairs it.

The refutation probe should be promoted from scratch to a durable artifact. Two options for the
plan to choose between:

- **Preferred**: adapt it into a regression witness in `CslibTests/` (task 553 already added
  `CslibTests/S4LoopGuardRegression.lean` — a natural neighbour). This makes the refutation
  *executable*, so any future attempt to re-add the lemma fails the test suite rather than
  rediscovering the obstruction a fifth time.
- **Minimum**: keep it in the specs tree and cite it from the relocated docstring.

The preferred option is strongly recommended. The whole reason this task exists is that the
obstruction kept getting rediscovered; a compiled countermodel is the only form of the finding
that cannot go stale.

## 7. Recommendation

**Route (c) — DELETE**, executed as:

1. Machine-check the refutation once more against the tree at implementation time (the probe
   file is ready and currently passes).
2. Promote the countermodel to `CslibTests/` as an executable regression witness.
3. Relocate the obstruction record — now upgraded from "blocked" to "refuted", with the
   countermodel and the Massacci category-error note — into the `accPinnedBy` module comment.
4. Delete the section comment, docstring, and lemma (`FrameSoundness.lean:1159-1251`).
5. Reconcile the five prose/baseline records in §5, regenerating the axiom census with
   `--update` rather than hand-editing.
6. Update task 566's carve-out record to note its rationale has lapsed.
7. Verify: `lake build --wfail --iofail` emits **one fewer** `declaration uses 'sorry'` warning
   and no new warnings; `lake test` exit 0; `scripts/check-axiom-census.sh` green at the new
   57-row baseline.

**Justification in one line, for the commit and the docstring**: the lemma was deleted because
its statement is false — a machine-checked countermodel is included as a regression test — and
because the soundness obligation it was written to serve is discharged sorry-free by
`branchSatisfiableIn_s4FC_addEdge_of_blocked` and the `S4RedirectSoundInv` family.

### Anti-vacuity check

The task forbids closing the `sorry` by weakening the statement into something vacuous. Route
(c) does not weaken anything: it removes a false assertion that nothing consumed, and replaces
it with a *stronger* and *true* artifact — a refutation. The satisfiability-preservation content
the lemma gestured at remains fully present in the tree, proven, in three places.

## 8. Risks and Open Items

- **Low risk overall.** No proof depends on the deleted declaration; the change is prose,
  deletion, one census regeneration, and one new test.
- **Requires reversing an explicit user decision.** The retention was user-directed and should be
  surfaced for confirmation at plan approval. The refutation is the new evidence that was not
  available when that decision was made.
- **Census regeneration must use `--update`.** `axiom-census-baseline.txt` is explicitly marked
  "do not hand-edit"; the ratchet in `scripts/check-axiom-census.sh` compares column 1 as an
  exact set.
- **Coordinate with task 566.** Its carve-out is now inert. Its Boneyard convention is unaffected
  (the lemma is *deleted*, not moved — the Boneyard is for zero-consumer code with retained
  provenance value, and a false statement's provenance value is fully captured by the relocated
  countermodel).

---

## Appendix: Artifacts Produced

| Path | Purpose |
|---|---|
| `specs/582_s4_ancestor_redirect_soundness_obstruction/scratch_refute_ancestor_redirect.lean` | Machine-checked refutation. `lake env lean` exit 0; axioms `[propext, Quot.sound]`; no `sorryAx` |
