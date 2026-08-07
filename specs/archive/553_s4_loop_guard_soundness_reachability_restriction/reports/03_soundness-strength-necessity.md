# Research Report: Is Full-Strength `branchSatisfiableIn s4FC` Necessary?

## Metadata

- **Date**: 2026-07-26
- **Task**: 553 `s4_loop_guard_soundness_reachability_restriction`
- **Started**: TBD
- **Completed**: TBD
- **Effort**: TBD
- **Dependencies**: TBD
- **Sources/Inputs**: TBD
- **Artifacts**: TBD
- **Standards**: TBD
- **Session**: `sess_1785084826_a33d36`
- **Agent**: cslib-research-hard-agent (`--hard --lit`, `orchestrator_mode: true`)
- **Focus prompt**: *Is the current strength of soundness necessary? Would weakening soundness
  cause problems for its downstream consumers?*
- **Reference grounding tier**: **Tier 1** (literature-backed) + Tier 3 (implementation-backed)
- **Read-only territory**: `Cslib/**` (no edits made; `FrameSoundness.lean:1244` `sorry` untouched)

---

## Verdict (stated first, per the deliverable contract)

> **WEAKENING IS SAFE.** Every consumer of the S4 soundness line — actual and planned — was
> enumerated by reference. **None of them requires `branchSatisfiableIn s4FC`.** The decisive
> structural fact is that the invariant is a *proof-internal device that never appears in the
> statement of any exported theorem*: `branchPropAdequateIn` has **zero** occurrences outside
> `FrameSoundness.lean`, and `branchSatisfiableIn` has zero **S4** occurrences outside it. The
> decidability instance — the consumer the task description singles out — is built from
> `modalTableauX φ = .closed → s4Valid φ`, a statement in which no invariant occurs at all, and
> both endpoints of the weaker invariant's chain (`branchSatisfiableIn_imp_branchPropAdequateIn`,
> `modalClosed_unsat_propAdequateIn`) are **already landed, sorry-free, machine-verified**.

**Mandatory caveat, stated with equal force:** *safe* is not *free*, and *safe* is not
*feasible*. The reason to weaken was to make preservation tractable, and the weaker invariant
has its **own** documented, unresolved preservation defect
(`reports/02_...md` §5.1) that afflicts even plain mint-edge chains. Authorizing option (2)
buys the removal of a **statement-level** obstruction; it does not buy a proof. See §7 and §10.

---

## 1. Reference Grounding (H3)

### 1.1 BibKey verification against `references.bib`

| BibKey | `references.bib` line | Used for |
|---|---|---|
| `Massacci2000` | `references.bib:1010` | Loop-checking discipline, Technique 8.2, Def. 8.1/8.2, Lemma 8.2 |
| `Gore1999` | `references.bib:1023` | Named only to record it is **not** the blocker (per dispatch instruction) |
| `Blackburn2001` | `references.bib:65` | Cited by `instDecidableS5Valid`'s docstring (§6.6 p.382) |
| `ChagrovZakharyaschev1997` | `references.bib:75` | Canonical-model/completeness standard reference |
| `Fitting1983` | `references.bib:211` | `FrameSoundness.lean`'s own module `## References` |

All five BibKeys verified present. No new BibKey needs to be added for this report.

### 1.2 Source-to-implementation mapping

| Source claim | BibKey | Chunk / locus | Lean target | Translation note |
|---|---|---|---|---|
| Loop checking = "stopping the search whenever two prefixes are a different name for the same state"; a prefix σ is a *copy* of σ′ iff they carry the same formulas | `Massacci2000` §8.1 | `~/Projects/Literature/massacci_2000_single_step_tableaux_for_modal_logics/chunk_0029.md` | `blockingWorldS4Keyed` (`LoopChecking.lean:506`) | CSLib compares *recorded birth keys*, not live content — the "staleness" defect (`LoopChecking.lean:469-490`) |
| Technique 8.2: "**Before reducing a π-formula, check whether the corresponding prefix is not a copy of a shorter prefix.**" | `Massacci2000` §8.1 | `chunk_0030.md` | — (no CSLib analogue) | **Massacci blocks by WITHHOLDING the π-rule. He adds NOTHING.** CSLib instead emits `(.linear [], acc.addEdge sf.label wBlock)` (`LoopChecking.lean:753,758`) |
| Theorem 8.1: "If the L-tableau ... terminates with a π-completed branch, then A is L-satisfiable" | `Massacci2000` §8.1 | `chunk_0030.md` | `modalTableauS4Keyed_complete` (`FrameCompleteness.lean:4265`) | Massacci's loop-checking theorem is **completeness-side only**. He has *no* soundness obligation from blocking, because a blocked branch is a **subset** of an unblocked one |
| Def. 8.2 (*modal copy*, "same ν formulae"); "For K4 or S4 Theorem 8.1 can be extended to π-modal-completeness" | `Massacci2000` §8.1 | `chunk_0030.md` | `successorBirthContent` / `S4LoopInv.keyLowerBd` | Confirms the S4-specific box-only key notion CSLib uses is the literature-standard one |
| Pruning Lemma 8.2 (blocked subtrees may be deleted, preserving π-completeness) | `Massacci2000` §8 | `chunk_0031.md` | — | The literature's *countermodel* construction identifies copies; it does not record a redirect edge |

**The load-bearing literature finding** (new to this report, and directly relevant to §7):
`Massacci2000`'s loop-checking is *purely subtractive*. Technique 8.2 withholds a rule
application; it never adds a formula, a world, or an edge. That is exactly **why** the standard
treatment has a trivial soundness story and an interesting completeness story. CSLib's
`modalApplyOneS4Keyed` inverts this: at a blocked minting shape it emits **no formulas but
still adds an edge** (`LoopChecking.lean:753`, `:758`), manufacturing a soundness obligation
that the source calculus does not have. This is the root of the entire task-553 difficulty.

---

## 2. What each invariant asserts, and exactly how much weaker the weak one is

### 2.1 `branchSatisfiableIn` (`FrameSoundness.lean:110-118`)

```lean
def branchSatisfiableIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' → m.r (f w) (f w')) ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)
```

### 2.2 `branchPropAdequateIn` (`FrameSoundness.lean:1264-1276`)

```lean
def branchPropAdequateIn (FC : FrameCondition)
    (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (acc : Accessibility) : Prop :=
  ∃ (W : Type) (m : Model W Atom) (f : WorldIndex → W),
    FC m.r ∧
    (∀ w w', acc.hasEdge w w' = true →
      (∀ ψ, (⟨.pos, .box ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        Satisfies m (f w') (.box ψ)) ∧
      (∀ ψ, (⟨.neg, .diamond ψ, w⟩ : SignedFormula (Proposition Atom) WorldIndex) ∈ b →
        ¬ Satisfies m (f w') (.diamond ψ))) ∧
    ∀ sf ∈ b,
      (sf.sign = .pos → Satisfies m (f sf.label) sf.formula) ∧
      (sf.sign = .neg → ¬Satisfies m (f sf.label) sf.formula)
```

**Exactly one conjunct differs.** The `FC m.r` conjunct and the entire branch-formula conjunct
are byte-identical. The edge conjunct changes from *"the recorded edge is a real `m.r` edge"* to
*"whatever propagation payload the edge could ever transmit is already true at its target"*.

### 2.3 The gap, characterized concretely

The weakening is **strict**, and the essential difference is that the weak edge conjunct is
**local and non-composing** — it says nothing about chains.

**Concrete separator** (constructed for this report; small enough to check by hand):

- `b := [T(□p)@0, F(p)@2]`, `acc := {0→1, 1→2}`.
- **Not** `branchSatisfiableIn s4FC`: the two edges force `m.r (f 0) (f 1)` and `m.r (f 1) (f 2)`;
  `IsTrans` then forces `m.r (f 0) (f 2)`; `T(□p)@0` then forces `p` at `f 2`, contradicting
  `F(p)@2`.
- **Is** `branchPropAdequateIn s4FC`: take `W = {x,y,z}`, `m.r` = the identity (reflexive and
  transitive, so `s4FC` holds), `f 0 = x, f 1 = y, f 2 = z`, `p` true at `x` and `y`, false at
  `z`. Edge `0→1`: `T(□p)@0 ∈ b`, and `f 1 = y ⊨ □p` (under identity `r`, `□p` at `y` ⟺ `p` at
  `y` ✓). Edge `1→2`: no `T(□ψ)@1 ∈ b`, so the obligation is **vacuous** — the chain is cut here.
  Branch conjunct: `x ⊨ □p` ✓, `z ⊭ p` ✓.

So the branches that separate the two are exactly those where a box-fact must travel **more than
one recorded edge**. This is the same phenomenon report 02 §5.1 identified from the other side
("that weakening **destroys frame transitivity as a usable lever**") and the reason
`branchPropAdequateIn_s4FC_boxPos_trans_mem` (`:1322`) carries the extra `hready` hypothesis
that `branchSatisfiableIn_s4FC_boxPos_trans_mem` (`:1085`) does not.

### 2.4 Machine-verified bridge facts

| Fact | Locus | `lean_verify` result |
|---|---|---|
| `branchSatisfiableIn_imp_branchPropAdequateIn` (sat ⟹ adequate) | `FrameSoundness.lean:1284` | `{"axioms":[],"warnings":[]}` — **zero axioms**, sorry-free |
| `modalClosed_unsat_propAdequateIn` (closed ⟹ ¬adequate) | `FrameSoundness.lean:1481` | `{"axioms":["propext","Quot.sound"],"warnings":[]}` — sorry-free, standard axioms only |

These are the **two endpoints of the soundness chain**, and both are already landed for the
weak invariant. This is the single most decision-relevant measurement in this report.

---

## 3. Consumer enumeration (by reference, not by assumption)

### 3.1 Repo-wide occurrence census

```
grep -rc "branchSatisfiableIn" Cslib/ --include=*.lean | grep -v ":0"
  Cslib/Logics/Modal/Tableau/FrameSoundness.lean:147
  Cslib/Logics/Modal/Tableau/GenericDriver.lean:1        (prose comment, :145)
  Cslib/Logics/Modal/Tableau/FrameCompleteness.lean:5    (all reflFC / symmFC — T and B, not S4)

grep -rn "branchPropAdequateIn" Cslib/ --include=*.lean | grep -v FrameSoundness.lean
  (no output — ZERO occurrences outside FrameSoundness.lean)

grep -rn "\bs4Valid\b" Cslib/ CslibTests/ --include=*.lean   →  9 hits, of which
  exactly ONE is a theorem statement: FrameCompleteness.lean:4265 (modalTableauS4Keyed_complete)
  exactly ONE is the definition:     FrameSoundness.lean:1051
  the remaining 7 are prose/docstrings.
```

**There is no cross-file consumer of the S4 invariant at all.** Both invariants are confined to
`FrameSoundness.lean`; the S4 instances of `branchSatisfiableIn` in `FrameCompleteness.lean` do
not exist (its five hits are `reflFC` at `:1105/:1209/:1216` and `symmFC` at `:1874/:1881`).

### 3.2 Consumer-by-consumer table

| # | Consumer | Locus | Strength it actually needs | Evidence |
|---|---|---|---|---|
| C1 | **`instDecidableS4Valid` / `s4Valid_decides`** (does not exist yet) | would sit in `FrameCompleteness.lean`, mirroring `:2407-2421` | **Neither** — its inputs are `modalTableauX φ = .closed → s4Valid φ` and `s4Valid φ → ... = .closed`; no invariant occurs in either | `FrameCompleteness.lean:4174-4177`: *"The decidability half (`s4Valid_decides`/`instDecidableS4Valid`) remains out of scope until both a genuine soundness theorem and this completeness theorem exist for the same driver."* See §4 |
| C2 | The (unwritten) S4 soundness capstone `modalTableauS4*_sound` | would sit in `FrameSoundness.lean` | **Neither** — its statement is `... = .closed → s4Valid φ`. The invariant is the induction hypothesis inside its proof, not part of its type | Compare `modalTableauS5_sound` (`FrameSoundness.lean:3373`), whose statement is `modalTableauS5 φ = .closed → s5Valid φ` |
| C3 | `modalTableauS4Keyed_complete` | `FrameCompleteness.lean:4265` | **Neither.** Consumes `s4Valid φ₀` as a hypothesis and produces `.closed`. Reads no invariant | Read in full: `:4265-4301` routes through `modalExpandBranchesS4Keyed_hintikka`, `modalOpenBranchS4_countermodel`, `extractModelS4`. `branchSatisfiableIn` appears nowhere |
| C4 | The 4-rule adequacy lemmas `modalFourBoxProp_sound_adequate`, `modalFourDiaNegProp_sound_adequate`, `branchPropAdequateIn_boxPos_mem` | `:1391`, `:1413`, `:1443` | **Weak only** — already written against `branchPropAdequateIn` and landed sorry-free | Their statements name `branchPropAdequateIn` directly |
| C5 | `S4LoopInv` / termination line (`modalStepBranchS4_preserves_S4LoopInv`, `modalStepBranchS4_worldBound`, fuel sufficiency) | `LoopChecking.lean:7519` and feeders | **Neither.** `S4LoopInv`'s ten fields are purely syntactic/combinatorial (`keysDistinct`, `keyLowerBd`, `bClosure`, `outDegEq`, …). No semantic invariant appears | `LoopChecking.lean:7513-7518`: *"All ten fields are now fully closed, zero sorry"*; the whole file has **zero** `branchSatisfiableIn` occurrences |
| C6 | `CslibTests/S4LoopGuardRegression.lean` | `CslibTests/S4LoopGuardRegression.lean` | **Neither** — `#eval`-only corpus over `modalExpandBranchesS4Keyed`; asserts computational verdicts | Grep shows only `s4Valid` prose and `s4Verdict` `#eval`s |
| C7 | The K / T / B / S5 / Five / KB5 soundness lines | `FrameSoundness.lean` (`trivialFC`, `reflFC`, `symmFC`, `s5FC`, `fiveFC`, `kb5FC`) | **Full strength — but of their own `FC`, not `s4FC`.** They are unaffected: `branchPropAdequateIn` is S4-specific (`FrameSoundness.lean:1284` and all its consumers are stated at `s4FC` literally) | Weakening the S4 invariant is a strictly local change; no other corner's proof mentions it |

**Zero consumers require `branchSatisfiableIn s4FC`.**

---

## 4. The decidability instance specifically (the key sub-question)

The dispatch names this as the single most important sub-question. The answer is grounded in
the codebase's own written statement of intent and in the completed S5 template.

### 4.1 What the instance is made of

```lean
-- FrameCompleteness.lean:2407-2409
theorem s5Valid_decides (φ₀ : Proposition Atom) :
    modalTableauS5 φ₀ = .closed ↔ s5Valid φ₀ :=
  ⟨modalTableauS5_sound φ₀, modalTableauS5_complete φ₀⟩

-- FrameCompleteness.lean:2418-2421
instance instDecidableS5Valid (φ₀ : Proposition Atom) : Decidable (s5Valid φ₀) :=
  match h : modalTableauS5 φ₀ with
  | .closed => .isTrue ((s5Valid_decides φ₀).mp h)
  | .openBranch _ _ => .isFalse (fun hv => by rw [modalTableauS5_complete φ₀ hv] at h; cases h)
```

**No invariant appears anywhere in this construction.** The instance consumes exactly two
theorems, each of whose statements mentions only `modalTableauX`, `.closed`, and `xValid`.
This is identically true of `instDecidableTValid` (`:1311`), `instDecidableBValid` (`:1925`),
`instDecidableFiveValid` (`:3208`), `instDecidableKb5Valid` (`:4154`), and
`instDecidableKValid` (`CompletenessLoop.lean:2293`) — six landed instances, one uniform shape.

The codebase states the S4 requirement in exactly these terms
(`FrameCompleteness.lean:4174-4177`, quoted verbatim):

> The decidability half (`s4Valid_decides`/`instDecidableS4Valid`) remains out of scope until
> both **a genuine soundness theorem and this completeness theorem exist for the same driver**.

### 4.2 Can the decidability half be built on `branchPropAdequateIn`-strength soundness?

**Yes.** The "closed ⟹ valid" implication the instance needs decomposes into three obligations,
all of which the weak invariant supports:

| Obligation | With `branchSatisfiableIn s4FC` | With `branchPropAdequateIn s4FC` | Status |
|---|---|---|---|
| **(a)** Initial: `¬ s4Valid φ` ⟹ invariant holds at `([F(φ)@0], Accessibility.empty)` | direct construction (cf. `FrameSoundness.lean:3328-3334`) | same construction, **or** free via `branchSatisfiableIn_imp_branchPropAdequateIn` (`:1284`). Edge conjunct is vacuous over `Accessibility.empty` | ✅ **weak version already available, zero-axiom** |
| **(b)** Preservation: every step preserves the invariant | blocked — `FrameSoundness.lean:1244` `sorry`; plan v3 `#### Phase 2 Verdict` | **the open work** (§7, `hready` / report 02 §5.1) | ⚠️ open in **both** |
| **(c)** Closed leaf: `isModalClosed b` ⟹ ¬ invariant | `modalClosed_unsatIn` (`:139`) | `modalClosed_unsat_propAdequateIn` (`:1481`), verified sorry-free | ✅ **weak version already landed** |

The direction of the logic is worth stating explicitly, because it is the point where an
intuition can go wrong. A **weaker** invariant makes obligation (a) *easier* (satisfiability
implies it) and obligation (c) *harder* (fewer things refute it). Obligation (c) is the one
that could in principle break under weakening — and it **does not**, because a classically
closed branch carries an explicit `T(ψ)@w` / `F(ψ)@w` pair (or `T(⊥)`), and the branch-formula
conjunct — the conjunct that refutes it — is **byte-identical** in the two definitions. The
landed proof at `:1481` opens with `intro ⟨W, m, f, _, _, hb⟩`, discarding the edge witness
entirely, and is documented as a *"direct transcription"* of `modalClosed_unsat`.

**Conclusion for C1:** the decidability instance does not merely *tolerate* the weaker
invariant — it cannot even observe which invariant was used, because the invariant is
existentially quantified inside a proof and never surfaces in a type.

---

## 5. The S5 precedent

**S5 uses full strength — but got it for free, and for a reason that provably does not transfer
to S4.**

- The S5 fuel induction concludes `List.Forall₂ (fun b acc => ¬branchSatisfiableIn s5FC b acc)`
  (`FrameSoundness.lean:3306`), and `modalTableauS5Gen_sound` (`:3317`) builds its initial
  witness as a full `branchSatisfiableIn s5FC` (`:3328-3334`). So: full strength, yes.
- **But S5's redirect edges are genuine `m.r` edges.** `modalApplyOneS5w` is a *witness-reuse*
  rule, structurally the same "reuse an existing world instead of minting" move as the S4 guard.
  Its soundness docstring (`:3356-3361`) says so directly: *"a reuse edge only ever connects two
  worlds already known to the branch, and under `s5FC` — whose relation is an equivalence — any
  two worlds reachable from the common origin `0` are related
  (`accReachableInv_related_s5`)."*
- `accReachableInv_related_s5` (`:1858-1866`) proves `m.r (f w) (f w')` for **any** two known
  worlds, by two applications of `reachable_imp_related_s5` composed with one more
  `rightEuclidean` step (`:1845-1850`). The whole argument rests on `s5FC.2` being
  `Relation.RightEuclidean` — i.e. on **symmetry**.
- `s4FC = Std.Refl ∧ IsTrans` has **no symmetry**. The task description already records this
  ("the S5 precedent relies on symmetry so it does not transfer"), and the divergence audit
  re-derived it independently (`reports/02_...md` §5, note on option (c)).

**Evidential weight:** the S5 precedent is *neutral-to-favourable* for weakening, and
specifically it is **not** evidence that full strength is necessary. S5 never had to *pay* for
full strength — it fell out of the frame condition. Where the payment is genuinely due, the S5
line does something different: it does not thread bare `branchSatisfiableIn` through the
induction, it threads a **bespoke composite invariant** `S5SoundInv` (`:3304`, `:3335-3338`,
combining `accFreshInv` + `accReachableInv` + `accTargetsKnown`) and *derives* the
`branchSatisfiableIn` conclusion at the end. That is itself a precedent for "use whatever
invariant the induction needs; state the capstone in `xValid` terms."

---

## 6. Related blocked tasks — real coupling, verified from `specs/state.json`

None of #511, #506, #548, #300 declares a `dependencies` edge on 553 (verified: #511 `deps=[535]`,
#506 `deps=[511]`, #548 `deps=[511,535]`, #300 `deps=[506]`). Real coupling assessed below.

| Task | Status | What it actually needs from 553 | Needs full strength? |
|---|---|---|---|
| **#300** `modal_extensions_t_s4_s5` | `[blocked]`, deps `[506]` | Its description is explicit and terminal: *"This umbrella closes when S4 decidability (`instDecidableS4Valid`) lands."* That is C1 | **No.** It names the `Decidable` instance, not an invariant |
| **#506** `s4_loopchecking_machinery_termination_bound_and_decidability` | `[blocked]`, deps `[511]` | *"establish fuel sufficiency, and state `s4Valid` / `Decidable (s4Valid phi)` against `Cube.S4`"* — its S4 soundness clause is *"Prove S4 soundness via `Satisfies.four`"*, a **rule-level** semantic fact | **No.** Rule-level soundness (`Satisfies.four`) is orthogonal to the branch invariant; both `branchSatisfiableIn_s4FC_boxPos_trans_mem` (`:1085`) and its adequacy analogue (`:1322`) already exist |
| **#511** `s4_loop_checking_termination` | `[blocked]`, deps `[535]` | Pigeonhole world bound, `S4LoopInv`, `modalStepBranchS4_worldBound`, then *"Phase 9: fuel sufficiency, `s4Valid` completeness, `Decidable (s4Valid phi)`"* | **No.** Entirely syntactic/combinatorial; `LoopChecking.lean` has **zero** `branchSatisfiableIn` occurrences |
| **#548** `decidability_remaining_eight_modal_cube_corners` | `not_started`, deps `[511,535]` | *"transitive corners (K4, K45, D4, D45) reuse the S4 loop-checking mechanism"* | **⚠️ The one genuine risk.** See below |

### 6.1 The #548 risk (the strongest case against weakening — reported honestly)

`branchPropAdequateIn_boxPos_mem` (`FrameSoundness.lean:1443`) discharges its central step using
`s4FC`'s **reflexive** half:

```lean
have hboxw' : Satisfies m (f w') (.box φ) := (hedgeconj w w' hedge).1 φ hmem
have hsatw' : Satisfies m (f w') φ  := hboxw' (f w') (hFC.1.refl (f w'))   -- :1454
```

The weak edge conjunct only ever delivers `□φ` at the target; recovering the **unwrapped** `φ`
there requires `Std.Refl`. Under full `branchSatisfiableIn` this step is instead the direct
edge `m.r (f w) (f w')` (cf. `modalApplyOne_boxPos_sound`, K's own arm) and needs **no**
reflexivity at all. Consequently, if #548's transitive-but-**not**-reflexive corners (K4, K45,
D4, D45) literally reuse an adequacy-style invariant, this lever is unavailable and the
adequacy line would need a modification those corners do not currently have.

Weight of this risk, assessed:

1. #548 is `not_started` and blocked on two upstream tasks; it is a *hypothetical* consumer.
2. #548's own acceptance criterion explicitly permits *"an explicit documented out-of-scope note
   per corner stating why"* — it does not require a uniform mechanism.
3. #548 also offers an escape hatch it already names: *"Where filtration/FMP is cheaper than
   loop-checking for a given corner, route via FMP instead"* (`FmpMeasure.lean` exists, 3388
   lines, and has **zero** `branchSatisfiableIn`/`branchPropAdequateIn` occurrences).
4. Most importantly: a K4 corner reusing the *mechanism* would need its own `k4FC`-instantiated
   invariant regardless. Nothing about landing S4 at `branchPropAdequateIn s4FC` forecloses
   landing K4 at `branchSatisfiableIn k4FC` — the S4 weakening is a **local** choice inside one
   file's S4 section.

I rate this a **real but deferred and routable** risk, not a blocking requirement.

---

## 7. Is there a middle option?

Two concrete candidates were found in the existing record. Neither is invented for this report.

### 7.1 Middle **invariant**: the disjunctive edge conjunct (report 02 §5.1)

```
∀ w w', acc.hasEdge w w' → (m.r (f w) (f w')) ∨ (the current propagation-adequacy clause)
```

This is genuinely between the two:

- `branchSatisfiableIn s4FC` ⟹ disjunctive (take the left disjunct).
- disjunctive ⟹ `branchPropAdequateIn s4FC`: the left-disjunct case is discharged by exactly
  the argument already written at `FrameSoundness.lean:1290-1301` (transitivity + the branch
  conjunct); the right-disjunct case is immediate.

Its purpose is precisely to fix the §5.1 defect: *"genuine mint edges keep transitivity (making
`hready` free again, as it is for `branchSatisfiableIn`) and only redirect edges take the
weakened clause."* The audit is explicit that its preservation across redirect steps is
**unverified**: *"I have not verified that this disjunctive form is preserved across redirect
steps — that is a design question for the planner, not a finding."*

**Assessment:** this is the strongest candidate on the table. It is strictly stronger than
option (b)'s target, it directly addresses the §5.1 defect that would otherwise sink option (b),
and it costs nothing at the consumer end (see §3-§4: the consumers cannot observe the choice).
It does, however, still fail to make `branchSatisfiableIn_s4FC_ancestor_redirect` provable —
the redirect edge still takes the weak disjunct.

### 7.2 Middle **driver**: literature-standard subtractive blocking (`Massacci2000` Technique 8.2)

Make the blocked case emit `(.linear [], acc)` — **no edge**. Then the blocked step is trivially
sound for **full** `branchSatisfiableIn s4FC` (nothing added to `b`, `acc` unchanged), and the
task's entire soundness problem evaporates without weakening anything. This is what
`Massacci2000` actually does (`chunk_0029.md`, `chunk_0030.md`); it is why his loop-checking
theorem (Thm 8.1) is completeness-side only.

**Honest cost, stated so this is not read as a free lunch:** the redirect edge is load-bearing on
the **completeness** side. `modalOpenBranchS4_countermodel` / `extractModelS4` build the
countermodel from `acc`; without the edge, a blocked `F(□φ)@w` has no successor in the extracted
model and the truth lemma fails at exactly that world. `Massacci2000` solves this by
*identifying* copies (Def. 8.1/8.2 + Pruning Lemma 8.2, `chunk_0031.md`) — a quotient
construction, not an edge. Adopting this would mean **redoing** the already-landed
`modalTableauS4Keyed_complete` (`FrameCompleteness.lean:4265`) against a quotient extraction.
That is a large, but literature-guided and structurally standard, piece of work.

I flag §7.2 because the user is choosing between routes and it was not among the three options
presented; it is not a recommendation.

---

## 8. Decision table

| Route | Soundness target | Consumer-sufficient? | Remaining proof obligation | Landed assets reused |
|---|---|---|---|---|
| **(1)** Full driver-dependent Hintikka/canonical-model truth lemma → full `branchSatisfiableIn s4FC` | full | Yes (trivially — strongest) | Large new construction: a truth lemma pinning the witness model, defeating the "existentially arbitrary `m.r`" obstruction (plan v3 Phase 2 Verdict, steps 1-3) | `modalClosed_unsatIn` (`:139`); the `s4FC` rule lemmas `:1085`/`:1106`/`:1129`/`:1149` |
| **(2)** Accept `branchPropAdequateIn s4FC` | weak | **Yes — every consumer verified in §3** | Preservation only. But the §5.1 `hready` defect is unresolved and afflicts plain mint chains, not just redirects | `branchSatisfiableIn_imp_branchPropAdequateIn` (`:1284`, 0 axioms); `modalClosed_unsat_propAdequateIn` (`:1481`); `:1322`, `:1356`, `:1391`, `:1413`, `:1443` — **seven landed lemmas** |
| **(2′)** Disjunctive edge conjunct (§7.1) | middle | Yes (implies the weak one) | Preservation across redirect steps — *explicitly unverified* by the audit | Most of (2)'s assets, with proof edits |
| **(3)** Subtractive blocking, no redirect edge (§7.2, `Massacci2000` Tech. 8.2) | full, for free | Yes | Redo completeness against a quotient/copy extraction | All of `FrameSoundness.lean`'s `s4FC` full-strength lemmas; **loses** `modalTableauS4Keyed_complete` |

---

## 9. Answer to the literal question

**Is the current strength of soundness necessary?** — **No.**

**Would weakening cause problems for its downstream consumers?** — **No.** Enumerated by
reference in §3: C1 (`instDecidableS4Valid`), C2 (the soundness capstone), C3
(`modalTableauS4Keyed_complete`), C5 (`S4LoopInv`/termination), C6 (the regression corpus) each
need **neither** invariant, because none of them mentions one; C4 (the 4-rule adequacy lemmas)
already needs only the weak one; C7 (K/T/B/S5/Five/KB5) is untouched because the weakening is
S4-local. The one hypothetical exception, C-#548's non-reflexive transitive corners (§6.1), is
`not_started`, doubly blocked upstream, explicitly permitted to route via FMP or to document a
per-corner out-of-scope note, and in any case free to instantiate its own invariant.

**Therefore the cost of route (1) is not justified *by consumer requirements*.** If route (1) is
chosen it must be for a different reason — e.g. that a full truth lemma is judged more likely to
close than route (2)'s preservation obligation, or that a canonical/pinned witness model is
wanted for its own sake.

**And the symmetric warning:** route (2) is not thereby *cheap*. Its blocker moves from a
statement-level impossibility (plan v3 Phase 2 Verdict: the witness model is existentially
arbitrary) to an unresolved preservation defect (report 02 §5.1: `hready` fails on plain
mint-edge chains). Any plan built for route (2) **must** sequence the §5.1 repair — most
plausibly §7.1's disjunctive edge conjunct — as its **first** phase, exactly as report 02's own
recommendation stipulated (*"with a mandatory precondition that the §5.1 invariant defect is
planned for first"*).

**Evidence-supported route: (2′) — option (2)'s weakened target, entered via §7.1's disjunctive
edge conjunct, with §5.1 as Phase 1.**

---

## 10. Adversarial Self-Verification (H4)

I attempted to refute my own conclusion ("weakening is safe") by constructing the strongest case
that some consumer breaks.

| # | Claim | Source / attempted counterexample | Verdict |
|---|---|---|---|
| 1 | The decidability instance never mentions the branch invariant | `FrameCompleteness.lean:2407-2421` read in full; same shape at `:1311`, `:1925`, `:3208`, `:4154`, `CompletenessLoop.lean:2293` | **CONFIRMED.** Six landed instances, uniform shape, zero invariant references |
| 2 | `branchPropAdequateIn` has zero consumers outside `FrameSoundness.lean` | `grep -rn "branchPropAdequateIn" Cslib/ --include=*.lean \| grep -v FrameSoundness` → empty | **CONFIRMED** (mechanical) |
| 3 | Closed ⟹ ¬weak-invariant genuinely holds (the obligation weakening could break) | *Attempted refutation:* find a closed branch that is `branchPropAdequateIn`. Blocked by `modalClosed_unsat_propAdequateIn` (`:1481`), `lean_verify` → axioms `["propext","Quot.sound"]`, no `sorry` | **REFUTATION FAILED — claim stands.** The refuting conjunct is byte-identical across both definitions |
| 4 | Initial-config obligation holds for the weak invariant | `branchSatisfiableIn_imp_branchPropAdequateIn` (`:1284`), `lean_verify` → `{"axioms":[],"warnings":[]}`; edge conjunct is vacuous over `Accessibility.empty` | **CONFIRMED, zero axioms** |
| 5 | The weakening is strict (there is a real gap) | Separator constructed in §2.3: `b = [T(□p)@0, F(p)@2]`, `acc = {0→1,1→2}`, `W={x,y,z}`, `m.r` = identity, `p` true at `x,y` only | **CONFIRMED by hand-check. NOT machine-checked** — this is the least-verified claim in the report. It is corroborative (report 02 §5.1 reaches the same conclusion from the `hready` side), not load-bearing for the verdict |
| 6 | **Strongest counter-case:** #548's K4/K45/D4/D45 corners break under weakening | `branchPropAdequateIn_boxPos_mem` uses `hFC.1.refl` at `FrameSoundness.lean:1454`; `k4FC`-style conditions have no `Std.Refl`. The full-strength route needs no reflexivity here | **PARTIALLY UPHELD.** A real technical dependence exists. Mitigated by: #548 `not_started` + doubly blocked; its acceptance permits FMP routing or per-corner out-of-scope notes; and each corner may instantiate its own invariant. **Reported as a live risk, not dismissed** |
| 7 | Attempted counter-case: the completeness line secretly needs `branchSatisfiableIn s4FC` | Read `modalTableauS4Keyed_complete` (`:4265-4301`) in full; it routes through `_hintikka`, `_openBranch_initial_mem`, `modalOpenBranchS4_countermodel`, `extractModelS4`. Repo-wide grep confirms `FrameCompleteness.lean`'s only 5 `branchSatisfiableIn` hits are `reflFC`/`symmFC` | **REFUTATION FAILED — claim stands** |
| 8 | Attempted counter-case: the termination/`S4LoopInv` line needs it | `LoopChecking.lean` has **zero** `branchSatisfiableIn`/`branchPropAdequateIn` occurrences (10,352 lines). `S4LoopInv`'s ten fields are combinatorial (`:7513-7518`) | **REFUTATION FAILED — claim stands** |
| 9 | The S5 precedent proves full strength is needed | `modalTableauS5Gen_sound` does target `branchSatisfiableIn s5FC` (`:3306`, `:3328`), **but** via `accReachableInv_related_s5` (`:1858`), which is `rightEuclidean`-driven, i.e. symmetry. `s4FC` has none | **REFUTED as evidence for necessity.** S5 shows full strength is *achievable when symmetry is present*, not that it is *required*. S5's own induction runs on a bespoke `S5SoundInv`, not bare `branchSatisfiableIn` |
| 10 | Route (2) is therefore cheap / recommended without qualification | Report 02 §5.1: `hready` fails on a **plain mint-edge chain** (`0→1`, `1→2`, late-arriving `T(□ψ)@0`) — no redirect involved | **MY OWN CONCLUSION QUALIFIED.** "Safe for consumers" ≠ "provable". §9 now states the §5.1 precondition as mandatory, and §7.1 is promoted to the evidence-supported route |
| 11 | §7.2 (subtractive blocking) is a free win | Would invalidate the landed `modalTableauS4Keyed_complete`, since `extractModelS4` needs the edge to witness a blocked `F(□φ)@w` | **QUALIFIED.** Reported with its cost; flagged as *not* a recommendation |
| 12 | The `Gore1999` gap is the blocker | Per dispatch instruction, treated as settled; independently, plan v3's escalation branch records *"The `Gore1999` escalation branch does not apply"* | **CONFIRMED settled.** No literature-acquisition phase proposed |

### Claims modified after this pass

- The headline verdict was tightened from "weakening is safe" to "weakening is safe **for
  consumers**, but safety ≠ feasibility" (row 10). The §5.1 precondition was promoted from a
  footnote to a mandatory Phase 1 in §9.
- The recommended route was changed from bare (2) to **(2′)** (disjunctive edge conjunct), on
  the strength of row 10.
- §6.1 was added as a standalone section rather than a table cell, because row 6 was only
  *partially* refuted and deserves visibility.

### Confidence levels

| Finding | Confidence |
|---|---|
| No consumer requires `branchSatisfiableIn s4FC` (§3, §4) | **High** — mechanical grep + full reads of every candidate + two `lean_verify` runs |
| The decidability instance is invariant-agnostic (§4) | **High** — six landed instances of identical shape + the codebase's own written statement at `:4174-4177` |
| S5 does not establish necessity (§5) | **High** — `accReachableInv_related_s5`'s proof is `rightEuclidean`-only |
| The §2.3 separator | **Medium** — hand-checked, not machine-checked; corroborative only |
| #548 risk assessment (§6.1) | **Medium** — the reflexivity dependence at `:1454` is verified; the *routability* judgment is a judgment |
| §7.1 disjunctive form is preserved across redirect steps | **Unknown** — explicitly unverified by report 02; flagged as the load-bearing open question, **not** asserted |

### Zero-debt compliance

No recommendation in this report involves deferring a `sorry`, adding an axiom, or introducing
a vacuous definition. The `sorry` at `FrameSoundness.lean:1244` was **not** touched, per the
user's explicit instruction that it remain as a documented marker. No `Cslib/**` file was edited.

---

## 11. Memory candidates

1. **Invariant strength is a proof-internal choice when the capstone is stated in `xValid`
   terms.** In the CSLib modal tableau line, all six landed `Decidable (xValid φ)` instances
   consume only `modalTableauX φ = .closed ↔ xValid φ`. Any branch invariant is existentially
   quantified inside the soundness proof and is invisible to consumers — so "does a consumer
   need the stronger invariant?" is usually answerable by grep alone.
2. **`Massacci2000` loop-checking is subtractive.** Technique 8.2 withholds the π-rule at a copy
   prefix and adds nothing; the literature's loop-checking theorem (Thm 8.1) is therefore
   completeness-side only. A driver that instead *adds a redirect edge* manufactures a soundness
   obligation the source calculus does not have. Worth checking before porting any blocking
   discipline.
3. **S5's witness-reuse soundness is symmetry-driven, not reuse-driven.**
   `accReachableInv_related_s5` (`FrameSoundness.lean:1858`) relates any two known worlds via
   `rightEuclidean`. Reflexive-transitive (S4) frames have no analogue, so the S5 reuse pattern
   never transfers to S4 by structural analogy.
