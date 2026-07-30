# Blocker Research: Gap 1 Fixpoint-Completeness — and a Machine-Verified Refutation Downstream of It

- **Task**: 430 - prove_atom_persistence_upward_closure_for_intexpan
- **Type**: cslib, blocker-escalation research
- **Session**: sess_1785374640_65c34b
- **Plan**: `plans/06_gate-b2-then-origin-tracing-export.md` (Phase 10 `[BLOCKED]`, Phase 11 `[NOT STARTED]`)
- **Blocker researched**: handoff 10's new blocker — "origin tracing is necessary but not
  sufficient; the residual `x < y ≤ l` sub-case reduces to the pre-existing open Gap 1
  fixpoint-completeness question"
- **`Cslib/` writes**: **none**. `git status --short Cslib/ CslibTests/` empty at end of dispatch.
- **New scratch artifacts** (both compile clean, `lake env lean`, zero errors):
  - `scratch/Gap1FixpointProbe.lean`
  - `scratch/BetaSplitRefutation.lean`

---

## Verdict (two parts, both explicit)

### Part 1 — The delegated question: Gap 1 fixpoint-completeness is **PROVABLE**

Not merely provable: the load-bearing lemma is **already landed, sorry-free, in the current
tree**, and the per-arm instantiation the blocker needs is a six-line composition identical to
one Phase 7 already landed and built green.

### Part 2 — But it does not unblock anything: the residual case is **REFUTED**

Granting Gap 1 collapses the residual obligation from four arms down to exactly one — the
positive-disjunction (beta) arm — and **that arm is now refuted by a machine-verified
counterexample against the real `intuitionisticTableau` and the real `minimalTableau`.** The
augmented-frame persistence statement that Phases 7-13 exist to prove is **false**.

**Consequently the task's overall verdict is REFUTED**, and the plan's sanctioned terminal-deferral
contingency applies — see §6 for the deferral-scope question the delegation asked about.

---

## 1. Part 1 in detail: Gap 1 is provable, and nearly already proved

### 1.1 What `applyPersistenceFixpoint` can actually fail at

`Expansion.lean:188-194`:

```lean
def applyPersistenceFixpoint (b : IBranch Atom) (edges : IEdges) (fuel : Nat) : IBranch Atom :=
  match fuel with
  | 0 => b
  | fuel' + 1 =>
    let b' := applyAllTImpRules b edges
    if b'.length == b.length then b   -- fixpoint reached
    else applyPersistenceFixpoint b' edges fuel'
```

`applyAllTImpRules b edges = b ++ newForms.flatten ++ genCopies.flatten` is purely additive, so
length-equality **is** genuine fixpoint-ness — this is exactly the landed
`applyAllTImpRules_eq_self_of_length_eq` (`Scheme.lean:5335`). The `if` exit is therefore always a
genuine fixpoint. **The only non-genuine exit is `fuel = 0`.** Gap 1 is thus purely a
fuel-sufficiency question, nothing more.

### 1.2 The fuel-sufficiency lemma is landed

`Scheme.lean:5386`, sorry-free, and its own docstring already claims the closure:

```lean
private lemma applyPersistenceFixpoint_genuine_of_count_le_fuel
    {φ0 : Proposition Atom} {edges : IEdges} (b : IBranch Atom) (fuel : Nat)
    (hb : ∀ x ∈ b, x ∈ intUniverseExt φ0)
    (hfuel : (intUniverseExt φ0).countP (fun sf => !(b.any (· == sf))) ≤ fuel) :
    applyAllTImpRules (applyPersistenceFixpoint b edges fuel) edges
      = applyPersistenceFixpoint b edges fuel
```

It is stated for **arbitrary** `b` and **arbitrary** `fuel`. Nothing about it is specific to the
terminal arm of the `key` induction.

### 1.3 Both hypotheses are already in scope at *every* arm, including the reuse arm

- `hb` comes from `IAllUniv φ0 branches`, threaded through the whole `key` induction.
- `hfuel` comes from `IAllFuel φ0 branches expandedSets fuels`, which supplies
  `intWork (intUniverseExt φ0) bh eH < f`, and `intWork U b e` is *by definition*
  (`Scheme.lean:4253`) the sum of the two `countP`s — so the `b`-side `countP` is `≤ f` by `omega`.
- `applyPersistenceFixpoint` is called at `Scheme.lean:4865` as
  `applyPersistenceFixpoint b edges f` with exactly the branch's own `f`. So `hfuel`'s `fuel`
  argument is the right one.

**Verified by direct source reading of both arms:** the terminal arm (`case4`) derives this at
`Scheme.lean:7008-7017`, and the reuse arm (`case6`) already brings the identical hypotheses into
scope at `Scheme.lean:7173` (`hUnivP_head`) and `Scheme.lean:7180` (`hFuel_bh_eH`), because it
needs them to feed `ih`.

### 1.4 The lemma statement and proof route (what a Phase-11 dispatch would write)

At `case6`, after line 7180, insert verbatim:

```lean
have hfuel_bh : (intUniverseExt φ0).countP (fun sf => !(bh.any (· == sf))) ≤ f' + 1 := by
  simp only [intWork] at hFuel_bh_eH
  omega
have hgenuine : applyAllTImpRules bPers edgesH = bPers :=
  applyPersistenceFixpoint_genuine_of_count_le_fuel bh (f' + 1) hUnivP_head hfuel_bh
have hpp_reuse : IPosPersistRaw edgesH bPers := by
  intro χ w w' hacc hmem hw'
  exact applyPersistenceFixpoint_copy_complete (φ0 := φ0) hUnivP_head hfuel_bh hmem hacc hw'
```

`hgenuine` is Gap 1 at the reuse arm. `hpp_reuse` is its usable form (raw-edge copy-completeness
of the reuse-time snapshot).

`[UNVERIFIED]` — this block was **not** compiled, because the delegation prohibits modifying
anything under `Cslib/` and the declarations involved are `private` to `Scheme.lean`, so a scratch
file cannot call them. The grounding is: (a) the *identical three-step composition already
compiles* at `case4` (lines 7011-7017), (b) both hypotheses are present at `case6` under the same
names (lines 7173, 7180), and (c) `bPers` is the same `applyPersistenceFixpoint bh edgesH (f'+1)`
term at both arms. Risk of it not compiling is low but not zero.

### 1.5 Machine-checked empirical confirmation

`scratch/Gap1FixpointProbe.lean` instruments the recreated expansion loop with a counter
`nonGenuine`, incremented whenever `(applyAllTImpRules bPers edges).length ≠ bPers.length` — i.e.
whenever `bPers` is **not** a genuine fixpoint — at *every* loop iteration, not only terminal ones.

| candidate | iterations | `nonGenuine` | reuse events |
|---|---|---|---|
| `phiCanonical` | 41 | **0** | 8 |
| `phiRS` | 41 | **0** | 8 |
| `phiRS2` | 41 | **0** | 8 |
| `phiBeta2` | 30 | **0** | 6 |
| `phiS1` | 41 | **0** | 7 |
| `phiS2` | 41 | **0** | 7 |
| `phiS3` | 37 | **0** | 0 |

**272 loop iterations, zero non-genuine fixpoints.** The fuel budget was never the binding
constraint on the persistence sub-recursion on any run.

### 1.6 The Gap-1 STOP-gate note in `Scheme.lean` is stale

`Scheme.lean:553-573` still reads *"Gap 1 (fuel entanglement) is UNCHANGED and remains the sole
blocker … Establishing 'fuel is always sufficient …' needs a NEW step-lt-style measure lemma for
`applyPersistenceFixpoint`'s recursion … This measure has not been built."* That measure **has**
been built (§1.2), and the section header at `Scheme.lean:5094-5098` says so explicitly
("Closes GAP 1 of the `sat_timp` STOP-gate above"). The two notes contradict each other and the
stale one is what handoff 10 (correctly, given what it read) treated as an open question. A
docstring correction is warranted independently of everything else in this report.

---

## 2. What resolving Gap 1 buys — and what it leaves

Handoff 10 predicted origin-tracing would recurse without terminating favourably. With Gap 1 in
hand, the recursion is not needed at all, because the reuse-time containment invariant
**strengthens for free from `l` to the whole ancestor interval**:

> At reuse time, `bPers` is a genuine `applyAllTImpRules` fixpoint (§1). So for any raw ancestor
> `y` of `l` (and `l` carries branch entries), copy-completeness gives
> `posFormulasAt bPers y ⊆ posFormulasAt bPers l`. Composing with the reuse check's own
> containment conjunct `posFormulasAt bPers l ⊆ posFormulasAt bPers x` yields
> `posFormulasAt bPers y ⊆ posFormulasAt bPers x` **for every raw ancestor `y` of `l`.**

The right post-reuse invariant is therefore not handoff 07's `Q(b) := ∀χ, T(χ)@l ∈ b → T(χ)@x ∈ b`
but its interval strengthening:

```
Q'(b) := ∀ y, isAccessible E y l = true → ∀ χ, T(χ)@y ∈ b → T(χ)@x ∈ b
```

whose base case is the display above. Checking `Q'` against each arm that can add positive content
(handoff 10's own source enumeration 1-5):

| arm | closes `Q'`? | mechanism |
|---|---|---|
| `genCopies` copy from ancestor `z` of `y` | **yes** | `z` is an ancestor of `l` too, so `Q'` applies to `z` directly. **No `ForestComparable` case split needed at all.** |
| cross-world T-imp (`intTImpRule`) | **yes** | source `w` is an ancestor of `l`; `Q'` gives `T(φ→ψ)@x` and `T(φ)@x`; `IBranchSaturation.sat_timp` at `x` plus `no_contradiction` gives `T(ψ)@x` (handoff 07's argument, reused verbatim) |
| alpha (`T(θ∧ρ)@y`) | **yes** | `Q'` gives `T(θ∧ρ)@x`; final-branch `sat_tand` at `x` splits it |
| fresh-mint payload / initial content | **yes, vacuously** | mints create worlds with labels `≥ nw > l`, so no post-reuse mint payload ever lands at a world `≤ l`; initial content is in the snapshot |
| **beta (`T(θ∨ρ)@y`)** | **NO** | `Q'` gives `T(θ∨ρ)@x`, and `sat_tor` at `x` gives `T(θ)@x ∨ T(ρ)@x` — but the two occurrences are **distinct `ISF` entries** and split **independently**. Nothing forces them to pick the same disjunct. |

So Gap 1 does not merely reduce the residual — it eliminates origin tracing, the `ForestComparable`
case split, and handoff 10's non-terminating recursion, leaving **exactly one** arm. That arm is
Gate B2's residual risk, surfacing as an actual proof obstruction precisely as Gate B2's own
verdict predicted it would ("Phase 9 … is the load-bearing point where this risk would surface as
an actual proof obstruction if it is real").

---

## 3. Part 2 in detail: the beta arm is REFUTED

### 3.1 Why Gate B2's search missed it, and the sharper recipe

Gate B2 planted disjunctions into reuse-heavy formulas and hoped the two splits would diverge by
accident; its own verdict notes a counterexample "requires the disjunction to arrive at an
already-reuse-linked pair via a genuinely INDEPENDENT path strictly AFTER the reuse decision".
That framing is what made the search hard. The construction below instead **forces** the
divergence with a *closure asymmetry*, so nothing is left to accident:

1. `φ0 = (Γ → pr)`. `F(φ0)@0` mints world `1` carrying `F(pr)@1` and `T(Γ)@1`. World `1` is the
   intended reuse **target** `x`.
2. `Γ` contains `pr ∨ ps`. So `T(pr ∨ ps)@1`. Its `T(pr)@1` child closes immediately against
   `F(pr)@1` — so the surviving branch **necessarily** resolves world `1`'s disjunction to `ps`.
   This choice is forced by closure, not left to chance. **This is the mechanism Gate B2 lacked.**
3. `Γ` also contains `(ps → (ps → pr)) → pb`, whose T-imp reflexive branching arm yields
   `F(ps → (ps → pr))@1` as its *first* child. That mints world `2` with `T(ps)@2`,
   `F(ps → pr)@2`. No reuse fires there (no world carries `F(ps → pr)`).
4. `F(ps → pr)@2` is then processed. Obligation `ψ = pr`; world `1` carries `F(pr)@1`, is a raw
   ancestor of `2`, has the smaller label, and does not force `pr`. Containment holds because
   world `2`'s positive content is world `1`'s plus `ps`, which world `1` already has. **Reuse
   fires with `(x, l) = (1, 2)`**, recording the loop-back edge `(1, 2)`.
5. `genCopies` already copied `T(pr ∨ ps)` from `1` to `2`. That copy is a distinct `ISF` entry,
   unexpanded, and it splits independently **after** the loop-back edge is recorded. Its
   `T(pr)@2` child does **not** close, because reuse suppressed creation of any world carrying
   `F(pr)` below `2`.

```lean
def phiRef1 : Proposition Nat := ((pr ∨ ps) ∧ ((ps → (ps → pr)) → pb)) → pr
```

(`pr = .atom 2`, `ps = .atom 3`, `pb = .atom 1`.)

`phiRef1` is **not** intuitionistically valid (take `pr` false, `ps` true: `ps → (ps → pr)` is
false, so the antecedent holds vacuously in its second conjunct while `pr` fails), so
`.openBranch` is the *correct* verdict. This is not a soundness anomaly — the defect is in the
countermodel the open branch yields.

### 3.2 Machine-verified results

`scratch/BetaSplitRefutation.lean`, `lake env lean`, **zero errors**:

| `#eval` | result | meaning |
|---|---|---|
| `report phiRef1 realFuel` | `("OPEN", 17, 2, [(1,0),(2,1)], [(1,2),(2,2)], some (2,1,2))` | violation `(w,w',p) = (2,1,pr)` at the **real** fuel `intFuelExt phiRef1` |
| `atomTable phiRef1 realFuel` | `[(2,[2,3]), (1,[3]), (0,[])]` | world `2` forces `{pr, ps}`; world `1` forces `{ps}` only |
| `branchesAgree` | **`true`** | the recreated loop returns the *exact same branch* as the real `intuitionisticTableau phiRef1` |
| `decisiveFacts` | **`(true, false)`** | `intExtractValuation b 2 pr` holds; `intExtractValuation b 1 pr` does not |
| `fimpWitnesses` | **`[1]`** | world `1` is the *unique* world on `b` carrying `T(ps)` and `F(pr)` |
| `reportMin phiRef1 realFuel` | `("OPEN", 17, 2, …, some (2,1,2))` | same violation under `isMinimallyClosed` (DP-4's calculus) |
| `minBranchesAgree` | **`true`** | recreation matches the real `minimalTableau phiRef1` too |

Three of four targeted candidates refute: `phiRef1`, `phiRef3`, `phiRef4` all report
`some (2,1,2)`; `phiRef2` (disjunction reused as the antecedent) does not.

### 3.3 Why this is a refutation of the statement, not of a proof route

- `intExtractValuation b w p` unfolds to exactly `b.any (fun sf => sf.sign == .pos &&
  sf.formula == .atom p && sf.label == w)` (`Soundness.lean:1129`) — the probe tests the real
  valuation, not a proxy.
- The augmented edge list is a proof-side ghost witness, so the probe reconstructs it. The
  reconstruction is transcribed from the real `key` induction, **verified by direct source
  reading**: the reuse arm appends `augH ++ [(x, l)]` (`Scheme.lean:7322, 7349`), the mint arm
  appends `newE`, every other arm carries `augH` unchanged. `l = newE.2` is the label of the
  processed `F(φ → ψ)`.
- Direction convention checked against source: `isAccessible edges a b = true` means `a` is an
  ancestor of `b`, hence `a ≤ b` via `intAccessPreorder_le_of_isAccessible`
  (`Scheme.lean:280`); `isAccessible` is already the full transitive-closure DFS, so a single
  `isAccessible` check *is* the preorder check. The loop-back edge `(1,2)` gives
  `isAccessible aug 2 1 = true`, i.e. `2 ≤ 1`; the raw edge `(2,1)` gives `1 ≤ 2`. Worlds `1` and
  `2` are preorder-**equivalent**, exactly as report 05 §4 predicted, yet disagree on `pr`.
- **The choice of ghost witness cannot rescue it.** Any admissible augmented list must satisfy
  `IExpandedAccessConsistent` for the reused obligation `F(ps → pr)@2`, i.e. must make some world
  carrying `T(ps)` and `F(pr)` accessible from `2`. `fimpWitnesses = [1]` (machine-checked)
  shows world `1` is the only candidate on `b`. So **every** admissible list has `2 ≤ 1`, and
  upward closure then demands `pr` at world `1`, which fails.

`[UNVERIFIED]` — the step from `fimpWitnesses = [1]` to "the whole `∃ edges` conjunct of
`openBranch_countermodel` is false for this `b`" is a proof-level argument, not machine-checked:
it assumes `¬IForces` is only obtainable through `truthLemma`'s `IFimpAccess` route. Hand-checked
supporting evidence: over the **raw** frame `[(1,0),(2,1)]` upward closure *does* hold, but
`IForces (intExtractValuation b) 0 phiRef1` is then **true** (the antecedent fails at every world,
because `pb` is forced nowhere), so the raw frame does not witness the existential either.

---

## 4. Secondary finding: reuse can record a self-loop

The loop-back list for `phiRef1` is `[(1,2), (2,2)]`. The `(2,2)` entry is a reuse event with
`x = l = 2`: `intFImpReuseWitnessAnc?`'s guard is `x.ble w` (non-strict) and
`isAccessible edges w w` is reflexively true, so a world can discharge its own obligation against
itself. Harmless for persistence (a self-loop adds no new `≤` pair), but it means the augmented
frame carries reflexive edges that no existing docstring mentions. Recorded, not pursued.

---

## 5. What is now known that was not before (do not re-derive)

1. Gap 1's fuel-sufficiency side is **landed**, general in `b` and `fuel`, and instantiable at
   *every* arm — the STOP-gate note claiming otherwise is stale (§1.2, §1.6).
2. Granting Gap 1, the reuse-containment invariant strengthens from `{l}` to *all raw ancestors of
   `l`* for free, eliminating origin tracing, the `ForestComparable` case split, and handoff 10's
   non-terminating recursion (§2). **Phase 10's remaining task list is therefore unnecessary
   work, independent of the refutation** — worth recording in case any part of the augmented-frame
   route is ever revisited.
3. Exactly one arm survives that strengthening: beta (§2 table).
4. That arm is refuted, by a *closure-asymmetry* construction that forces the divergence rather
   than hoping for it — the recipe is §3.1 and it worked on the first attempt (§3.2).
5. Gate B2's PASS is **superseded**, by its own explicit supersession clause.

---

## 6. Implications for DP-3 / DP-4 / DP-5, and the deferral-scope question

The delegation asks specifically whether the plan's pre-authorized permanent deferral — scoped to
a *Gate-B2* refutation, and Gate B2 passed — applies here, or must be extended.

**It applies directly, by the plan's own supersession clause; no extension is needed.** Gate B2's
verdict (`handoffs/04_gate-b2-verdict.md`, closing bullets) states verbatim: *"If either phase
discovers a genuine obstruction traceable to this exact mechanism, that discovery supersedes this
PASS and the plan's Rollback/Contingency for a later-phase failure applies."* This refutation is
traceable to exactly that mechanism — independent beta-splits at two augmented-equivalent worlds —
and was found by a sharper construction inside the same search space, not by a different
mechanism. The plan's Rollback/Contingency row (*"Gate B2 refutation ⇒ terminal deferral of
DP-3/DP-4/DP-5 … permanent deferral is the sanctioned terminal answer for all three at once.
Escalation to the quotient/blocking-frame route is explicitly prohibited"*) therefore fires as
written.

Two consequences the plan's contingency did **not** anticipate, which a follow-up must handle:

1. **Phase 6's landed conjunct is itself false, not merely deferred.** The plan asserted
   *"Phase 6's statement-shape fix remains worth landing even in this branch, since it converts an
   unfillable sorry into an honestly-stated one."* That is now wrong: the upward-closure conjunct
   added to `openBranch_countermodel`'s conclusion (the `sorry` at `Scheme.lean:~7884`) is **false
   for `phiRef1`** (§3.3). It is not an honestly-stated deferred obligation; it is an unfillable
   one. Leaving it as a bare `sorry` with a "pending Phases 7-11" annotation would misrepresent
   the state of knowledge. It must be re-annotated as refuted, with the counterexample cited, or
   the conclusion re-stated over a frame that omits loop-back edges (which then breaks
   `¬IForces` — see §3.3, so this is a calculus-level redesign, not a restatement).
2. **This is a defect in the loop-check as a frame construction, not only in a proof.**
   `intFImpReuseWitnessAnc?` verifies `Sfor`-containment *at reuse time* and the recorded
   loop-back edge is never re-validated. Subsequent independent beta-splits at the two now-equated
   worlds break the equation. Termination (task 574's concern) is unaffected; countermodel
   *soundness* is not. Any future repair has to make the loop-check either re-validatable, or
   robust to post-reuse beta-splits (e.g. by expanding a disjunction at most once per
   equivalence class, or by refusing reuse when either world carries an unexpanded positive
   disjunction). **Both are calculus-level changes and both are out of this task's scope.** The
   quotient/blocking-frame route stays prohibited.

Per-sorry disposition:

| sorry | site | disposition |
|---|---|---|
| DP-3 | `Intuitionistic/Completeness.lean:~140` | terminal deferral; consumes a false premise |
| DP-4 | `Minimal/Completeness.lean:~141` | terminal deferral; refuted independently under `isMinimallyClosed` (§3.2) |
| DP-5 | `Scheme.lean:~731` (`truthLemma` T-imp) | terminal deferral; depends on the same augmented frame |
| Phase-6 conjunct | `Scheme.lean:~7884` | **re-annotate as REFUTED**, not deferred — this is new work, see consequence 1 above |

---

## 7. Recommended next dispatch

Not a build-out. A short, documentation-and-annotation dispatch:

1. Re-annotate the four sorries above per §6, citing `scratch/BetaSplitRefutation.lean` and
   `phiRef1` as durable anchors (no task numbers in `Cslib/`).
2. Correct the stale Gap-1 STOP-gate note at `Scheme.lean:553-573` (§1.6) — it contradicts the
   landed `applyPersistenceFixpoint_genuine_of_count_le_fuel` and the section header at `:5094`.
3. Document the loop-check's post-reuse beta-split defect (§6 consequence 2) at
   `intFImpReuseWitnessAnc?`'s docstring, as a recorded limitation with the counterexample cited.
4. Mark Phase 10 `[COMPLETED WITH EXCLUSIONS]` and Phases 11-13 likewise, with this report as
   evidence; Phase 14's final-CI bar (no `sorryAx`) is unreachable and should be re-scoped.
5. Optionally: land §1.4's six lines anyway. They are cheap, sorry-free, and Gap 1 is a
   genuinely useful fact — but they buy nothing for DP-3/DP-4/DP-5 and should not be presented as
   progress toward them.

Do **not** dispatch Phase 10's remaining origin-tracing task list. It was already unnecessary
given Gap 1 (§5 item 2), and is now moot.
