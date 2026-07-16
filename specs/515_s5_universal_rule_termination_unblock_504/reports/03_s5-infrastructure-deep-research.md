# S5 Tableau Decidability: What Infrastructure CSLib Actually Needs

**Task**: 515 — S5 universal rule termination (unblock 504)
**Date**: 2026-07-15
**Status**: Research complete. Confident recommendation.

Every claim below is marked **VERIFIED** (I read the file:line, or executed it against the real
repo this session via `lean_run_code`) or **INFERRED** (reasoned, not mechanized). No `.lean` file
was edited.

---

## 1. Verdict

**Build a witness-reuse S5 rule with a linear a-priori world budget, keep the unmodified generic
driver, and instantiate the entire termination stack at K's *own* universe (`modalUniverse` /
`modalWorldBound` / `modalFuel`) — deleting `modalUniverseS5` and `modalWorldBoundS5` outright.**

Concretely: replace the two world-**minting** arms of `modalApplyOneS5` (`T(◇φ)@w`, `F(□φ)@w`) with
a reuse test — if any known world already carries the witness `⟨s,φ,w'⟩`, add the edge `w→w'` and
emit `.linear [⟨s,φ,w'⟩]`; mint a fresh world only when no witness exists anywhere on the branch.
Leave the S5 universal-propagation arms (`T(□φ)`, `F(◇φ)`) **completely untouched**. Then bound the
world count by a monotone-injection argument (each mint permanently consumes a distinct
(sign, subformula) tag), and split `RuleApplicationSpec` so the Hintikka machinery no longer sees
the three fields S5 cannot discharge.

This is the synthesis of the two witness-reuse candidates, corrected by four facts I verified this
session that **no candidate design got fully right**:

1. **The fuel arithmetic forces K's universe.** `modalFuel` does **not** dominate the entry measure
   at `modalUniverseS5` — it fails at `atom` (19 > 8), `□p` (135 > 120), `p ∧ q` (779 > 120)
   [VERIFIED by execution]. Every design that instantiates the measure at `modalUniverseS5` and
   reuses `modalFuel` unchanged is broken. `modalUniverseS5` must be **deleted**, not preserved.
2. **The advertised escape hatch does not exist.** `modalWorldBoundS5 φ ≤ modalWorldBound φ` is
   **false**: `atom` gives 4 vs 1, `p ∧ q` gives 64 vs 9 [VERIFIED by execution]. It holds only at
   `□◇p` (64 vs 125) — the single formula the whole dossier was built on. The correct route is the
   linear bound instead, and I **proved `modalOps φ < modalWorldBound φ` sorry-free** this session.
3. **The rule must NOT be φ₀-parametrized.** `modalExpMeasure_step_lt_gen`'s `hOutputsSubsetUniverse`
   binds `φ0` **universally inside the hypothesis** (FmpMeasure.lean:3241) — so a φ₀-parametrized
   rule (`modalApplyOneS5a φ₀`, `modalApplyOneS5g phi0`) can *never* discharge it. The witness rule
   is plain `RuleApply Atom` and discharges it uniformly. **This single fact kills the
   static-pre-allocation design outright** and is the strongest argument for witness-reuse.
4. **The reuse arm must be guard-less.** Adding an `if acc.hasEdge w w' then (.notApplicable, acc)`
   guard makes `.notApplicable` reachable on a mint shape, which breaks the `exfalso` consumers at
   CompletenessLoop.lean:1049/1058 [VERIFIED by reading]. Always emit `.linear [witness]`. With the
   guard dropped I **proved the weakened F12′ sorry-free** this session.

Empirical validation of the recommended rule, executed against the **real** driver this session:
over an exhaustive **3963-formula** corpus (depth 2 over `{p, q, ⊥}` under `□,◇,→,∧,∨`),
differentially against an **exact S5 oracle**: **0 mismatches, 0 fuel-instability, 0 world-bound
violations**, with 1057 valid / 2906 invalid (non-vacuous).

**Recommended phase count: 12.** Not 7, not 8. See §5.

---

## 2. Why the Current Architecture Is Wrong

### 2.1 The shipped `modalTableauS5` diverges — it is *incorrect*, not merely unproven

**VERIFIED by execution.** On `T(□◇p)@0` — a formula with a **one-world** S5 model (a reflexive
point with `p` true) — the shipped driver's world count grows **exactly linearly in fuel**:

| fuel | 10 | 20 | 40 | 80 |
|---|---|---|---|---|
| `maxWorld` | 5 | 10 | 20 | 40 |
| `\|b\|` | 12 | 22 | 42 | 82 |

`maxWorld = fuel/2`, forever. It never saturates. Consequently
`modalHintikkaSetGen modalApplyOneS5 bR aR` — the exact Phase 8 goal — is **false at every fuel
value**. Phase 8 is not blocked; **its target is refutable**.

The docstring at S5Simplification.lean:1071-1073 asserts the opposite verbatim — *"S5 never mints a
world outside the K `diamondPos`/`boxNeg` arms, so `modalFuel` is sufficient here too"*. The second
half is **false** and must be deleted, not preserved. (The first half is true and is precisely why
the fix is local to minting.)

**Root cause, at file:line.** K's diamond-positive arm mints **unconditionally**:
`let w' := modalNextWorld b` (Rules.lean:103) — no reuse test, no guard. Contrast K's box-positive
arm at Rules.lean:96-97, which *is* guarded (`if newForms.isEmpty then (.notApplicable, acc)`).
Harmless under K (bounded modal depth); fatal under S5's universal box, which re-seeds `T(◇p)` at
every newly known world, each of which mints again.

**Gore predicted this exact failure in print.** Gore1999 (TR-ARP-15-95), TR p.48, on a static
building-up rule that is not "once off": *"it can lead to an infinite chain A ∈ w, ◇A ∈ w, ◇◇A ∈ w,
… so this system cannot give a decision procedure for S5 either."* [READ — see §9].

### 2.2 S5's true model bound vs CSLib's `2^(2|subfmls|)`

S5 is **NP-complete**, not PSPACE-complete, and has the polysize model property: an S5-satisfiable
φ has a model with at most `m+1` worlds, `m` = number of modality occurrences.

- **Blackburn2001 §6.6, p.382** [READ]: *"Given any S5 model for φ, it is possible to select m + 1
  points from this model (where m is the number of modality occurrences in φ) which suffice to
  construct a new S5 model for φ, and the NP-completeness of S5 follows straightforwardly. We leave
  the details as Exercise 6.6.4."*
- **Gore1999 TR pp.44-45** [READ]: the C†S5′ model graph — one successor per `¬□Qᵢ ∈ w₀`, all at
  level one, *"and stop!"*, `R` = the reflexive/transitive/symmetric closure of `≺`. `|W| = 1 + m`.
  That closure is **literally** CSLib's landed `Relation.EqvGen` countermodel.

CSLib's `modalWorldBoundS5 φ₀ = 2 ^ (2 * (modalSubfmls φ₀).length)` (S5Simplification.lean:73) is an
**exponential** bound mirrored from S4's loop-checking/pigeonhole architecture. It is *sound*, and it
was not a blunder — Gore p.48 shows that a **cut-free implicit** calculus with a universal
transitional rule genuinely does need the S4-style tree-of-clusters. But CSLib's tableau is
**labelled**, and the measured world count under witness-reuse is `≤ modalOps φ` — **linear**. On
`¬(◇p₁ ∧ … ∧ ◇p₉)` the real count is 9 while `modalWorldBoundS5` is 2⁶⁴ ≈ 1.8×10¹⁹.

**The user's central suspicion is correct — with one important correction.** "Mirroring S4 is the
wrong infrastructure for S5" is true **only conditional on also changing the rule set**. The
exponential bound cannot be shrunk while `modalApplyOneS5` is held fixed, because the *unguarded*
rule genuinely has no bound at all. The linear budget is a property **created by** the witness
guard, not a property of the shipped rule that better bookkeeping could recover.

**And the naive form of the suspicion is false.** "A linear budget from counting world-creating
subformulas" does **not** work by itself: `T(◇p)@0, T(◇p)@1, T(◇p)@2, …` are *distinct* signed
formulas, each firing its own mint. The budget is only valid when keyed on **(sign, body-subformula)
pairs**, which is exactly what the reuse test enforces.

### 2.3 `rankStep` is impossible — and it is not the only impossible field

`modalApplyOneS5_rankStep_not_dischargeable` (S5Simplification.lean:2995) is a landed, sorry-free
counterexample: `RuleApplicationSpec modalApplyOneS5` is **false**. Correct, and settled.

**But the dossier's framing that the spec "is false only at `rankStep`" is wrong.** I read the
structure (GenericDriver.lean:175-265). For any rule that adds an edge to an **existing** world,
**three** fields fail:

- `rankStep` (GenericDriver.lean:213) — the S5 counterexample.
- `knownWorldsStep` (GenericDriver.lean:245) — a **strict dichotomy**: either `.snd = acc`, or
  `.snd = acc.addEdge sf.label (modalNextWorld b)`. The reuse arm satisfies **neither** (it adds a
  real edge, to a world `≠ modalNextWorld b`). [VERIFIED by reading]
- `rankEdge`, inside `ModalPotentialInv` (FmpMeasure.lean:2326) — `∀ w w', acc.hasEdge w w' →
  rank w' + 1 = rank w`. Irreparably false: the saturated `□◇p` branch has a **reflexive** edge
  `(1,1)` [VERIFIED by execution], forcing `rank 1 + 1 = rank 1`.

**The good news, and it is the load-bearing structural fact of this report.** I extracted the spec
field usage of the five Hintikka-forcing lemmas (CompletenessLoop.lean:233-760):

```
3 spec.boxNegWitness      3 spec.boxPosNotExpanding    3 spec.diaNegNotExpanding
3 spec.diaPosWitness      8 spec.freshLocal            1 spec.localShapeInvariance
1 spec.outputsSubsetUniverse
```

**No `rankStep`. No `knownWorldsStep`. No `outDegStep`.** [VERIFIED]. The three impossible fields
are confined entirely to the `potentialInv`/`phiBound` path, whose *only* downstream product is the
single scalar `modalMaxWorld b < modalWorldBound φ0`
(`modalMaxWorld_lt_worldBound_of_phiBound`, CompletenessLoop.lean:775-776). **That scalar is all the
rank ever buys.** Supply it another way and the entire rank/potential/geomCap apparatus is bypassed
rather than fought.

Equally important: `modalExpMeasure_step_lt_gen` (FmpMeasure.lean:3231) takes `apply` plus **three
raw hypotheses** (`hBranchingLength`, `hPersistentFresh`, `hOutputsSubsetUniverse`) and a raw
`hW : modalMaxWorld bh < modalWorldBound φ0`. It mentions **neither `RuleApplicationSpec` nor
`rankStep`** [VERIFIED by reading the full signature]. The measure layer never needed the rank.

### 2.4 The keyed-vs-unguarded mismatch, and the missing Hintikka fields

`S5LoopInv` (S5Simplification.lean:1566, **12 fields**) is an invariant of the **keyed** stepper
`modalStepBranchS5gKeyed` (:1506). **No driver in the repo runs the keyed stepper** (VERIFIED: grep
finds only the stepper, no keyed driver). `modalTableauS5 φ = modalTableauGen modalApplyOneS5 φ`
(S5Simplification.lean:1074) runs the **unguarded** `modalStepBranchGen`. So `S5LoopInv` does not
apply to the shipped surface at all.

And `S5LoopInv` has **none** of `ModalLoopInvGen`'s Hintikka-forcing fields. I read the real field
list (CompletenessLoop.lean) — `ModalLoopInvGen` has **7** fields and is parametrized by
`(rank : WorldIndex → Nat)`:

```
potentialInv, phiBound, hintikkaInv, eBoxOnlyNeg, eBoxNegWitness, eDiamondOnlyPos, eDiamondPosWitness
```

[VERIFIED]. Several candidate designs asserted a flat field list (`bClosure`, `eClosure`,
`accFresh`, `accKnown`, `outDegEq`) — those live **inside** `ModalPotentialInv`, not in
`ModalLoopInvGen`. Any plan that budgets the invariant refactor from that mistaken list is
mis-sized: dropping `rank` is an **arity change** to the structure K/T/B share, not a field swap.

**A dossier contradiction, resolved.** Two angles measured `blockingWorldS5 = none` at every mint
(the **unkeyed** guard, :913); two others measured `blockingWorldS5Keyed` (:1443) firing correctly.
These are **different functions** and both measurements are true. The unkeyed guard is structurally
dead (its birth-content equality can never hold, because S5's universal box pollutes every world
post-birth). The keyed guard genuinely works. So the keyed assets are **not** dead because they
fail — they are dead for the reason in §6.

---

## 3. R7 Settled

**R7 (fuel domination) is REFUTED. Definitively, by execution. No experiment remains.**

The repo's own scope note (FrameCompleteness.lean:2245-2273) offers exactly two routes to close
Phase 8 item 4: *"either a driver over the keyed stepper … or a proof that K's `modalFuel` already
dominates the unguarded S5 expansion (plan risk R7, fuel domination)."*

**Route (b) is dead.** The worked trace, executed against the real
`modalExpandBranchesGen modalApplyOneS5` on `[T(□◇p)@0]`:

| fuel | 10 | 20 | 40 | 80 |
|---|---|---|---|---|
| `maxWorld` | 5 | 10 | 20 | 40 |

`maxWorld = fuel/2` **exactly**, with no fixpoint. The mechanism: `T(□◇p)@0` is `.persistent`, so it
never retires; it re-fires at the newest world `w`, emitting `T(◇p)@w`; that fresh signed formula is
`.linear`, so it fires **once** and mints `w+1`; the box re-fires there; repeat. The supply of
trigger formulas never runs out because each new world manufactures a new one.

Fuel domination is not a hard proof — **it is a false statement**. The expansion is unbounded, so no
fuel value dominates it. Corroborated independently: `bClosure` against `modalUniverseS5` holds at
fuel 60 (0 escapees) but **fails** at fuel 200 (72 escapees) and fuel 400 (272 escapees) — the
expansion escapes even the S5 universe, and `maxWorld` exceeds K's own `modalWorldBound = 125` at
fuel ≥ 252, while `modalFuel (□◇p) = 3^2520` is astronomically larger.

**A second, separate R7-shaped trap I settled — this one is new and no design got it right.**
Even with a *terminating* rule, `modalFuel` is **not** free if you keep S5's universe. The entry
obligation is `modalExpMeasure (U φ) [[F(φ)@0]] [[]] ≤ modalFuel φ`, i.e.
`3^entryWork ≤ 3^fuelExp`. Executed:

| φ | `entryWork` @ `modalUniverse` (K) | `entryWork` @ `modalUniverseS5` | `fuelExp` |
|---|---|---|---|
| `atom p` | 7 | **19** | 8 |
| `□p` | 79 | **135** | 120 |
| `p ∧ q` | 119 | **779** | 120 |
| `□◇p` | 1511 | 779 | 2520 |

`modalFuel` is calibrated **razor-thin** against K's own universe — margin of exactly **1** at both
`atom p` (7 ≤ 8) and `p ∧ q` (119 ≤ 120). It dominates K's universe at every point tested, and
**fails** at S5's universe at three of four. Therefore:

> **Any design that instantiates the counting measure at `modalUniverseS5` and reuses `modalFuel`
> unchanged is broken, regardless of how good its rule is.** The recommendation instantiates at
> **K's universe**, where `modalExpMeasure_entry_le_fuel` (FmpMeasure.lean:208) applies **verbatim**
> and `modalFuel` needs no re-derivation.

The enabling lemma, **proved sorry-free this session**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`):

```lean
lemma modalOps_lt_worldBound (φ : Proposition Atom) : modalOps φ < modalWorldBound φ
```

via `modalWorldBound φ = (2c+1)^(c+1) ≥ (2c+1)^1 = 2c+1 > c ≥ modalOps φ`. Note the `c = 0` case is
the tight one (`0 < 1 = 1^1`) — and note that the *naive* `2 * |modalSubfmls φ|` budget **fails**
there (2 > 1). **Counting modal-operator occurrences rather than subformulas is load-bearing, not
cosmetic.**

---

## 4. The Re-Firing Problem

**The brief's stated crux does not exist in this codebase, and I verified the exact line.**

The brief asserts that an already-expanded `T(□φ)` will not re-fire when a later rule mints a new
world, so `T(φ)@w''` never appears and completeness fails. This is false, twice over:

1. **`T(□φ)@w` can never enter the expanded set.** `modalStepBranchGen`'s `.persistent` arm is
   `some ([newForms ++ b], [expanded], newAcc)` (Saturation.lean:139-141) — it returns `[expanded]`
   **unchanged**, never `[expanded ++ [sf]]`. Contrast `.linear` at :136 and `.branching` at :138,
   which both **do** append `sf`. And `modalApplyOneS5`'s `.pos/.box` arm returns only
   `.persistent`/`.notApplicable` (S5Simplification.lean:307-313), never `.linear`/`.branching`. The
   initial expanded set is `[]` (Saturation.lean:366). So the box formula is never retired.
   [VERIFIED by reading]

2. **The design intent is stated outright.** Saturation.lean:39: *"`boxPos`/`diamondNeg`
   (persistent) re-fire when new successors are added."* GenericDriver.lean:278-291 confirms F9
   `boxPosNotExpanding` exists precisely because `.persistent` leaves `e` unchanged, with its
   payload existentially quantified so that *"S5's universal propagation"* can discharge it.

So: **no re-firing machinery, no stratified two-phase "create all worlds before firing boxes"
ordering, no fairness/round-robin rework is required.** Any plan phase proposing them is solving a
non-problem. This alone saves a wasted phase.

### The polarity is exactly backwards — and that is the real insight

Re-firing is not a bug to be fixed. **It is simultaneously the divergence engine of the shipped rule
and the mechanism that makes the recommended design complete.**

The universal box is **self-limiting as well as self-re-firing**. `modalS5BoxAll b φ _w` filters out
formulas already on `b` (`if b.any (· == sf) then none`, S5Simplification.lean:216-221), and the arm
returns `.notApplicable` when `allNew.isEmpty` (:311-313). So:

- **Applicable ⟺ some *known* world lacks the formula.** Bound the world set and the box saturates
  **by itself**.
- **It re-fires automatically at any genuinely new world** — which is exactly Hintikka conjunct 2.

These two properties are precisely complementary. The *only* missing ingredient is a bound on the
world set. **The recommended design leaves re-firing completely untouched and bounds MINTING
instead.**

Corroborated at the boundary: `□□p` (no minting formula under the box) **already saturates
correctly** under the shipped rule at every fuel. Divergence requires a *minting* formula under the
box. That is the exact interaction the witness guard severs — and it is why the fix is a ~14-line
change to one `def`, not new infrastructure.

**Traced under the recommended rule, executed on `T(□◇p)@0`:**

| fuel | 20 | 200 | 2000 |
|---|---|---|---|
| result | `maxW=1 len=5 edges=[(1,1),(0,1)]` | *identical* | *identical* |

Box fires `T(◇p)@0` → mints world 1 with `T(p)@1`, edge `0→1`, retires → box **re-fires**
`T(◇p)@1` (a genuinely new signed formula) → witness test finds world 1 already carries `T(p)`, so
it **reuses**: edge `1→1`, no new world, retires → box goes `.notApplicable`. **Saturated, 2
worlds**, stable across a 100× fuel range (genuine saturation, not exhaustion).

The reflexive edge `(1,1)` arises naturally and is **harmless**: `modalTruthLemmaS5` quantifies over
`Relation.EqvGen` of the edge set (`eqvGen_mem_modalKnownWorlds_iff`, FrameCompleteness.lean:1934),
which collapses all known worlds into one equivalence cluster regardless of edge shape. This also
resolves the dossier's open question about whether loop-back edges can witness a diamond: **they
can, and they do.**

### The one genuine obligation: retired formulas

`T(◇φ)@w` fires once and **is** retired to `e` (`.linear`), so the driver never re-examines it and
saturation alone says nothing about it. Its conjunct-4 obligation is carried by the invariant field
`eDiamondPosWitness`, and it stays true forever because both the edge `w→w'` and the formula
`⟨.pos,φ,w'⟩` are on the branch at retirement time, and **`Accessibility` and `b` are both monotone
under every driver arm** (Saturation.lean:136/138/141 all append). Nothing can invalidate a witness
once established; later mints only add worlds. [INFERRED — the monotonicity is VERIFIED; the
invariant preservation is not yet mechanized.]

---

## 5. Lemma-Level Build Plan

12 phases, each sized to ~one agent run (~100-500 lines). **Phase 0 is a 30-minute kill test and
must run first.**

Ambient context: S5Simplification.lean:54-56 (`namespace Cslib.Logic.Modal.Tableau`,
`open Cslib.Logic.Tableau Cslib.Logic.Modal`) and the file's `variable {Atom : Type*}
[DecidableEq Atom] [Hashable Atom]`. **No `Fintype Atom` is needed anywhere.**

### Phase 0 — Kill test (30 min, gates everything)

Verify `modalSubfmls` closure survives the `neg φ = φ.imp .bot` encoding, so that
`(s,ψ) ∈ mintTags φ₀` is derivable from the tag invariant in the mint case. **This is the single
load-bearing step of the counting argument.** If it fails, the linear bound fails and the fallback
(§7) applies. `Proposition` has 7 constructors — `atom, bot, imp, and, or, box, diamond` — with no
primitive negation (Basic.lean:72-88) [VERIFIED].

### Phase 1 — The rule + the free bridges *(all four already compiled this session)*

```lean
def witnessWorldS5 (b : List (SignedFormula (Proposition Atom) WorldIndex))
    (s : Sign) (φ : Proposition Atom) : Option WorldIndex :=
  (modalKnownWorlds b).find? (fun w' => b.any (· == (⟨s, φ, w'⟩ : SignedFormula _ _)))

/-- GUARD-LESS. Always `.linear [witness]` on a hit — never `.notApplicable`, never `.linear []`. -/
def modalApplyOneS5w : RuleApply Atom := fun sf b acc =>
  match sf.sign, sf.formula with
  | .pos, .diamond φ =>
    (match witnessWorldS5 b .pos φ with
     | some w' => (.linear [⟨.pos, φ, w'⟩], acc.addEdge sf.label w')
     | none => modalApplyOneS5 sf b acc)
  | .neg, .box φ =>
    (match witnessWorldS5 b .neg φ with
     | some w' => (.linear [⟨.neg, φ, w'⟩], acc.addEdge sf.label w')
     | none => modalApplyOneS5 sf b acc)
  | _, _ => modalApplyOneS5 sf b acc

theorem witnessWorldS5_mem (h : witnessWorldS5 b s φ = some w') : ⟨s, φ, w'⟩ ∈ b
theorem modalApplyOneS5w_boxPos_eq : modalApplyOneS5w ⟨.pos, .box ψ, w⟩ b acc
                                      = modalApplyOneS5 ⟨.pos, .box ψ, w⟩ b acc := rfl
theorem modalApplyOneS5w_diaNeg_eq : modalApplyOneS5w ⟨.neg, .diamond ψ, w⟩ b acc
                                      = modalApplyOneS5 ⟨.neg, .diamond ψ, w⟩ b acc := rfl
theorem modalApplyOneS5w_eq_of_not_mint_shape (h : ¬mint-shaped sf) :
  modalApplyOneS5w sf b acc = modalApplyOneS5 sf b acc
```

**COMPILED THIS SESSION**, sorry-free: `witnessWorldS5_mem` (2 lines,
`have := List.find?_some h; simpa using (List.any_eq_true.mp this)`; axioms `[propext, Quot.sound]`)
and **both** `rfl` bridges (axioms `[propext]`).

Three design constraints, each load-bearing:
- **`.linear [witness]`, not `.linear []`** — the cons is required for `freshLocal`'s right disjunct
  (`.linear (wsf :: rest) ∧ .snd = acc.addEdge sf.label wsf.label`). Note `wsf` is bound only as the
  **head of the linear output**; nothing requires `wsf.label = modalNextWorld b`, despite the
  docstring saying "fresh" [VERIFIED, GenericDriver.lean:181-190]. The landed `modalApplyOneS5g`
  emits `.linear []` (S5Simplification.lean:987) and **breaks this shape** — that is a genuine
  correction over the landed code.
- **`.linear [witness]`, not `.persistent []`** — `.persistent` with an empty payload returns `some`
  with `b` **and** `expanded` unchanged (Saturation.lean:141): an instant infinite loop.
- **No `hasEdge` guard** — see Phase 6.

### Phase 2 — The Hintikka congruence bridge *(compiled this session — land it early)*

```lean
theorem hintikka_congr (b) (acc) :
    modalHintikkaSetGen modalApplyOneS5w b acc ↔ modalHintikkaSetGen modalApplyOneS5 b acc
```

**COMPILED THIS SESSION, sorry-free, `#print axioms` = `[propext]`**, by:
```lean
unfold modalHintikkaSetGen
constructor <;> · rintro ⟨h1, h2, h3, h4⟩
                  refine ⟨h1, ?_, h3, h4⟩
                  intro sf hsf
                  have h := h2 sf hsf
                  rcases hs : sf.sign with _ | _ <;>
                    rcases hf : sf.formula with _|_|_|_|_|ψ|ψ <;> simp_all [modalApplyOneS5w]
```

**Why it works** [VERIFIED by reading Saturation.lean:460-480]: conjunct 2 binds
`let (result, _) := apply sf b acc` but then returns **literal `True`** at `| .neg, .box _` and
`| .pos, .diamond _` — `result` is **unused at exactly the two shapes the witness rule intercepts**.
Conjuncts 1/3/4 name no rule function at all.

**This is the single highest-value declaration in the plan.** It ports the entire landed countermodel
half — `modalTruthLemmaS5`, `modalOpenBranchS5_countermodel`, `hintikkaS5_box_pos`,
`hintikkaS5_diamond_neg`, `eqvGen_mem_modalKnownWorlds_iff`, `extractModelS5*` — **verbatim, with
zero edits to FrameCompleteness.lean**. It is strictly better than the two `rfl` bridges alone,
which are defeated by the 8 rewrites through `modalApplyOneS5_eq_of_not_boxPos_diaNeg` at
FrameCompleteness.lean:2096-2181. Land it in Phase 2 and the whole plan de-risks.

### Phase 3 — The linear budget arithmetic *(proved this session)*

```lean
def modalOps : Proposition Atom → Nat   -- modal-operator occurrences
lemma modalOps_le_complexity (φ) : modalOps φ ≤ modalComplexity φ
lemma modalOps_lt_worldBound (φ) : modalOps φ < modalWorldBound φ     -- ★ PROVED, sorry-free
def mintTags (φ₀) : Finset (Sign × Proposition Atom)   -- ◇ψ ↦ (pos,ψ); □ψ ↦ (neg,ψ)
lemma mintTags_card_le_modalOps (φ₀) : (mintTags φ₀).card ≤ modalOps φ₀
```

`modalOps_lt_worldBound` **proved sorry-free this session**. This is what lets `modalUniverse`,
`modalExpMeasure`, `modalExpMeasure_entry_le_fuel` and `modalFuel` be reused **verbatim**, and lets
`modalWorldBoundS5`/`modalUniverseS5` be **deleted** rather than parametrized. It single-handedly
retires the `(universe, worldBound)`-parametrization blocker that three dossier angles flagged.

### Phase 4 — Tag invariant (no world hypothesis — breaks the circularity)

```lean
def S5wTagInv (φ₀) (b) : Prop := ∀ x ∈ b, (x.sign, x.formula) ∈ signedSubfmls φ₀
def usedTags (φ₀) (b) : Finset (Sign × Proposition Atom) :=
  (mintTags φ₀).filter (fun p => b.any (fun x => x.sign == p.1 && x.formula == p.2))
lemma usedTags_mono (h : ∀ x ∈ b, x ∈ b') : usedTags φ₀ b ⊆ usedTags φ₀ b'
theorem modalApplyOneS5w_outputs_tags (hb : S5wTagInv φ₀ b) (hsf : sf ∈ b) : ...
```

`S5wTagInv` deliberately carries **no world-bound hypothesis**. This is necessary: the landed
`modalApplyOneS5_outputs_subset` (S5Simplification.lean:1330) takes
`modalMaxWorld b < modalWorldBoundS5 φ₀` as an **input**, so it cannot be used to *prove* the world
bound. The tag-only invariant breaks that circularity.

### Phase 5 — The counting crux *(the load-bearing new proof)*

```lean
def S5wWorldInv (φ₀) (b) : Prop := modalMaxWorld b ≤ (usedTags φ₀ b).card

theorem modalStepBranchS5w_preserves_worldInv
    (hT : S5wTagInv φ₀ b) (hW : S5wWorldInv φ₀ b)
    (h : modalStepBranchGen modalApplyOneS5w b e acc = some (bs, es, acc')) :
    ∀ b' ∈ bs, S5wTagInv φ₀ b' ∧ S5wWorldInv φ₀ b'

theorem modalMaxWorld_lt_worldBound_of_S5w (hT) (hW) : modalMaxWorld b < modalWorldBound φ₀
```

**The argument.** A mint fires only when `witnessWorldS5 b s ψ = none`, which is *equivalent* to
`(s,ψ) ∉ usedTags φ₀ b` (any `⟨s,ψ,w''⟩ ∈ b` puts `w''` in `modalKnownWorlds b`, Branch.lean:89, so
`find?` cannot miss it). The mint **emits its own witness** at `w' = modalNextWorld b =
modalMaxWorld b + 1` (Rules.lean:125, Branch.lean:99). So `modalMaxWorld` grows by 1 while
`usedTags` gains `(s,ψ)` — and since `b` only ever grows, that tag is **used forever after**, so it
can never mint again. Mints inject into `mintTags`. Every non-mint arm leaves `modalMaxWorld`
unchanged and `usedTags` monotone. Chain:
`modalMaxWorld b ≤ (usedTags φ₀ b).card ≤ (mintTags φ₀).card ≤ modalOps φ₀ < modalWorldBound φ₀`.

`modalMaxWorld_lt_worldBound_of_S5w` is the **drop-in replacement** for
`modalMaxWorld_lt_worldBound_of_phiBound` (CompletenessLoop.lean:775-776) — same conclusion, at K's
own bound, with **no rank, no potential, no pigeonhole, no powerset, no birth keys**.

**Empirically confirmed this session: 0 violations of `maxWorld ≤ modalOps φ` across all 3963
corpus formulas**, checked at saturation on every branch.

> **Trap the implementer must not step in** (this is real and cost a prior design): a `birth`
> function must **not** be defined concretely as "the least world carrying the pair". S5's universal
> box can later add `⟨s,φ,w''⟩` at a **smaller** world, so that formulation is **not
> step-preserved**. The `usedTags`-cardinality formulation above sidesteps this entirely by never
> naming a witness world.

### Phase 6 — Spec split + the one-token weakening

```lean
structure RuleApplicationSpecCore (apply : RuleApply Atom) : Prop where
  freshLocal, outputsSubsetUniverse, persistentFresh, branchingLength,
  localShapeInvariance, boxPosNotExpanding, diaNegNotExpanding,
  boxNegWitness', diaPosWitness'          -- witness world EXISTENTIAL, not `modalNextWorld b`

structure RuleApplicationSpec (apply) extends RuleApplicationSpecCore apply : Prop where
  rankStep, outDegStep, knownWorldsStep   -- the three fields S5 cannot discharge

theorem RuleApplicationSpec.toCore (spec : RuleApplicationSpec apply) : RuleApplicationSpecCore apply
theorem modalApplyOneS5w_specCore : RuleApplicationSpecCore (modalApplyOneS5w (Atom := Atom))
```

**Drop THREE fields, not one** — `rankStep`, `outDegStep`, **and `knownWorldsStep`**. All three are
confined to the potential/measure path; `modalStepBranchGen_knownWorlds` has **zero** consumers in
the Tableau directory.

`diaPosWitness'` **COMPILED THIS SESSION** sorry-free (axioms `[propext, Quot.sound]`), delegating
the `none` arm to the landed `modalApplyOne_diamondPos_witness`:
```lean
cases h : witnessWorldS5 b .pos ψ with
| some w' => exact ⟨w', [], by simp [modalApplyOneS5w, h], by simp [modalApplyOneS5w, h]⟩
| none => obtain ⟨hsnd, rest, hfst⟩ := modalApplyOne_diamondPos_witness b acc ψ w
          exact ⟨modalNextWorld b, rest, by simp [...], by simp [...]⟩
```

**This is exactly why the reuse arm must be guard-less.** [VERIFIED by reading
CompletenessLoop.lean:1049-1060]: the conjunct-3/4 saturated-leaf discharge is an **`exfalso`** that
derives a contradiction *from* `.notApplicable`:
```lean
· exfalso
  obtain ⟨-, rest, hlin⟩ := spec.diaPosWitness bR aR ψ' w
  rw [hlin] at hna; simp at hna
```
It consumes the **`.linear` shape**, not the witness world. A `hasEdge` guard makes `.notApplicable`
reachable and **inverts this proof from a refutation into a proof obligation**. Guard-less keeps
both `exfalso` proofs byte-identical.

K/T/B pay **nothing**: they instantiate via `where` syntax (GenericDriver.lean:335, TDriver.lean:847,
BDriver.lean:821), so `extends` keeps those blocks compiling; and they discharge the existential form
with `w' := modalNextWorld b` via a 3-line adapter. [The adapters are INFERRED-cheap; the K
instantiation shape is VERIFIED.]

### Phase 7 — Rank-free loop invariant

```lean
structure ModalLoopInvHintikka (apply) (φ0) (b e) (acc) : Prop where
  bClosure, eClosure, eNodup, accFresh, accKnown        -- from ModalPotentialInv, rank-free
  worldBound : modalMaxWorld b < modalWorldBound φ0     -- replaces potentialInv + phiBound
  hintikkaInv, eBoxOnlyNeg, eBoxNegWitness, eDiamondOnlyPos, eDiamondPosWitness
```

**The honest hazard, and the fix.** A judge correctly showed that a *bare* `worldBound` scalar is
**not step-preserved** (`n < WB` says nothing about `n+1 < WB`), and that K re-establishes `phiBound`
only via an exact conservation identity (CompletenessLoop.lean:812). The fix is **not** a bare
field — it is to parametrize over an auxiliary step-preserved predicate:

```lean
(Aux : List (SignedFormula (Proposition Atom) WorldIndex) → Accessibility → Prop)
(auxStep : Aux is preserved by modalStepBranchGen apply)
(auxBound : Aux b acc → modalMaxWorld b < modalWorldBound φ0)
```
K instantiates `Aux := fun b _ => ∃ rank, ModalPotentialInv φ0 b e acc rank ∧ phiBound`; S5w
instantiates `Aux := fun b _ => S5wTagInv φ₀ b ∧ S5wWorldInv φ₀ b`. **This is the correction that
makes the factoring actually inductive**, and it is why this phase is real work, not a rename.
`hintikkaInv` is cheap for the witness rule: `modalHintikkaClauseGen` returns **literal `True`** at
`| .box _` and `| .diamond _` (Completeness.lean, VERIFIED), so all mint shapes are trivial.

### Phase 8 — Step preservation
```lean
lemma modalStepHintikka_preserves_inv (hs : RuleApplicationSpecCore apply) ... :
  (∀ p ∈ newBs.zip newExps, ModalLoopInvHintikka ... p.1 p.2 newAcc) ∧ measure-drop
```
Port of `modalStepGen_preserves_invariant` (CompletenessLoop.lean:761-845) minus the two
`potential_step` lines, with `Aux` threaded.

### Phase 9 — The parametric Hintikka lift *(the big one; may split into 9a/9b)*
```lean
theorem modalExpandBranchesHintikka (hs : RuleApplicationSpecCore apply) (hAux …) … :
  modalExpandBranchesGen apply branches expandedSets accs fuel = .openBranch bR aR →
  modalHintikkaSetGen apply bR aR

theorem modalExpandBranchesGen_hintikka (…)   -- ★ K-facing name/statement UNCHANGED
```
Port of `modalExpandBranchesGen_hintikka` (CompletenessLoop.lean:876-1185, ~310 lines — a **double
induction**). **REGRESSION GATE**: the K-facing theorem must keep its **exact existing name and
statement** — TDriver.lean:911 and BDriver.lean:871 consume it *by name* with
`∃ rank, ModalLoopInvGen …` in the hypothesis. Re-derive it from the parametric lift at
`Aux := (∃ rank, …)`. If that re-derivation does not go through, **stop**: the factoring is wrong.

### Phase 10 — `accTargetsKnown` top-loop *(genuinely missing — VERIFIED absent)*
```lean
theorem modalExpandBranchesGen_openBranch_accTargetsKnown …
```
`grep` for `openBranch_accTargetsKnown` returns **zero hits** across `Cslib/` [VERIFIED]. The repo's
own scope note (FrameCompleteness.lean:2250-2253) says it is *"not yet built"* and prescribes the
fix: generalize `modalExpandBranchesGen_openBranch_accSourcesKnown`'s double induction (BDriver.lean:
1065-1205) over an arbitrary step-preserved predicate `P`, then instantiate at **both**. `~60-line
clone`. **`modalOpenBranchS5_countermodel` REQUIRES this as its `hTgt` argument** — several candidate
designs listed that theorem under "reuses" while never supplying its hypothesis. **Build this
regardless of route**: every design needs it.

### Phase 11 — Soundness re-proof *(the largest un-costed item)*
```lean
theorem modalTableauS5_sound (φ) (h : modalTableauS5 φ = .closed) : s5Valid φ   -- STATEMENT UNCHANGED
```
The new case is the reuse edge `w→w'` to an **existing** `w'` carrying `⟨s,φ,w'⟩`. Structurally
**easier** than the landed mint case: the world-assignment `f` is **not extended** (no mint), so the
only obligation is `m.r (f w) (f w')` for an existing `w'`. **The decisive reuse**:
`accReachableInv_related_s5` (FrameSoundness.lean:1381) — landed — states that *two known worlds,
both reachable from 0, are related in **any** model whose relation is an equivalence relation*. That
is exactly the obligation. [INFERRED, not mechanized — this is risk R1.]

**Known breakage**: `modalApplyOneS5_snd_eq` (S5Simplification.lean:340-351, "accessibility output is
unconditionally identical to K's") becomes **false** and must be restated. Blast radius is
**smaller than feared**: FrameSoundness.lean:1326 is inside `modalApplyOneS5_fresh_local`, which
stays reusable (the witness rule is *defeq* to `modalApplyOneS5` on all 12 non-mint arms); every
other site (S5Simplification.lean:1720/1868/1943/1953/2017/2025/2083, and :398) lives in the
S5g/keyed machinery this plan retires anyway. [INFERRED from the dossier's enumeration; **run
`lean_references` on `modalApplyOneS5_snd_eq` to confirm before Phase 11.**]

### Phase 12 — Assembly, demolition, CI
```lean
def modalTableauS5 (φ) : ModalTableauResult Atom := modalTableauGen modalApplyOneS5w φ  -- one line
theorem modalTableauS5_complete (φ) (h : s5Valid φ) : modalTableauS5 φ = .closed
instance instDecidableS5Valid (φ) : Decidable (s5Valid φ)
```
Plus: delete ~2,000 lines of dead code (§6); delete the false docstrings at S5Simplification.lean:40-45
and :1071-1073; `lake build`/`test`/`checkInitImports`/`lint-style`/`shake`; BibKey docstrings; and a
`#eval`-backed regression test in CslibTests (the exact S5 oracle from this session is the cheapest
correctness net available and is route-independent).

### Landed assets reused **verbatim**

| Asset | file:line | Note |
|---|---|---|
| `modalTruthLemmaS5` | FrameCompleteness.lean:2048 | via `hintikka_congr` |
| `modalOpenBranchS5_countermodel` | FrameCompleteness.lean:2288 | via `hintikka_congr` (+ Phase 10's `hTgt`) |
| `hintikkaS5_box_pos` / `_diamond_neg` | :1956 / :1995 | shapes the rule does not touch |
| `eqvGen_mem_modalKnownWorlds_iff`, `extractModelS5*` | :1934, :499-531 | loop-back edges inert |
| `modalS5BoxAll` / `modalS5DiaNegAll` + `_mem` | S5Simplification.lean:216-291 | **untouched — correct as they stand** |
| `modalApplyOneS5` | :300 | called for all 12 non-mint arms + the mint `none` branch |
| `modalApplyOne_diamondPos_witness` / `_boxNeg_witness` | Rules.lean | discharge the `none` arm |
| `modalExpMeasure` / `modalWork` / `_step_lt_gen` | FmpMeasure.lean:192/197/3231 | **spec-free — VERIFIED** |
| `modalUniverse` / `modalWorldBound` / `modalExpMeasure_entry_le_fuel` | FmpMeasure.lean:149/144/208 | **K's own — verbatim** |
| `modalFuel` | Saturation.lean:98 | **unchanged, no re-derivation** |
| `modalExpandBranchesGen` / `modalStepBranchGen` / `modalTableauGen` | Saturation.lean:122/201/363 | **generic driver UNMODIFIED** |
| `accReachableInv_related_s5` | FrameSoundness.lean:1381 | the reuse-soundness engine |
| `signedSubfmls` + `signedSubfmls_card_le` | LoopChecking.lean:290/298 | the card bound |
| `modalApplyOneS5_rankStep_not_dischargeable` | :2995 | **kept** as documentation |

---

## 6. What Gets Discarded

Plainly and unsentimentally: **roughly 2,000 of S5Simplification.lean's 3,041 lines become dead
code** — essentially all of Phases 2-7 of the prior effort. This is not code that was never written;
it is **CI-green, sorry-free, committed code being deleted**. That is the honest sticker price of
this recommendation and it should not be soft-pedalled.

| Asset | file:line | Why it dies |
|---|---|---|
| `modalWorldBoundS5`, `modalUniverseS5` + membership/length lemmas | :60-204 | **Must** die: `modalFuel` does not dominate the entry measure at this universe (`atom` 19 > 8) — VERIFIED. Keeping it *breaks the fuel*. |
| `blockingWorldS5`, `successorBirthContentS5`, `modalApplyOneS5g` | :888-1051 | The **unkeyed** guard provably never fires (`= none` at every mint): birth content is scanned trigger-world-**locally**, but S5's universal box broadcasts **globally**, so live sets are permanently a strict superset of birth content. |
| `blockingWorldS5Keyed`, `modalStepBranchS5gKeyed` | :1424-1549 | The keyed guard **works** — but no driver runs it, and one cannot be added cheaply: see below. |
| `S5LoopInv` (12 fields) + ~11 `modalStepBranchS5g_preserves_*` | :1566-2723 | Invariants of a stepper no driver runs; no Hintikka-forcing fields. |
| `modalKnownWorlds_length_le_worldBoundS5`, `S5LoopInv.worldBound` | :2724-2830 | The birth-key **pigeonhole**. Replaced by `modalOps_lt_worldBound` — a monotone injection, no powerset. |
| `modalApplyOneS5_snd_eq` and the acc-invariance chain | :340-351, :398 | Becomes **false** (the reuse arm adds an edge where K adds none). Must be restated. |
| Docstrings at :40-45 and :1071-1073 | | **Factually false.** "`modalApplyOneS5` never mints a world"; "`modalFuel` is sufficient here too". Delete, do not preserve. |

**Why the keyed assets die even though the keyed stepper genuinely works.** This is the decisive
cost fact, and it is *not* "the guard fails" (that was the **unkeyed** guard — a different function).
It is: **`modalExpMeasure_step_lt_gen` is stated for `modalStepBranchGen`** [VERIFIED]. The keyed
stepper threads `keys` and has a **different shape**, so a keyed driver **cannot consume the measure
engine at all** and would have to re-derive termination against FmpMeasure.lean's 3,392 lines — and
it could not reuse `modalExpandBranchesGen_hintikka`, the single most expensive landed asset. The
keyed route "preserves" ~1,900 lines only as **inputs to work that must still be written from
scratch**. The witness route keeps the generic driver and *re-instantiates* that induction. That is
the whole ballgame.

**Kept, and worth keeping**: `modalApplyOneS5_rankStep_not_dischargeable` (:2995) as landed
documentation of why the rank route is dead. **Add a sibling** refuting the Phase 8 goal for
`modalApplyOneS5` in the same `decide`-backed idiom — it converts "Phase 8 blocked" into "the Phase 8
target was refutable", which is a landable, sorry-free result and is the honest disposition of the
FrameCompleteness.lean:2245-2273 scope note.

---

## 7. Risks + Kill Conditions

**R1 — Soundness re-proof (highest, un-mechanized).** `modalTableauS5_sound` (FrameSoundness.lean:
2379) is stated for the unguarded rule; the statement stays identical but the proof must be re-run.
*Mitigation*: the reuse arm never mints, so `f` is not extended, and `accReachableInv_related_s5`
(FrameSoundness.lean:1381) is landed and is exactly the needed fact. *Kill*: if it exceeds ~400
lines, re-litigate the fork. **Probe it in scratch BEFORE committing to Phase 6+**, exactly as
`hintikka_congr` and `diaPosWitness'` were probed this session.

**R2 — Phase 0 tag closure.** If `(s,ψ) ∈ mintTags φ₀` is not derivable from `S5wTagInv` under the
`neg φ = φ.imp .bot` encoding, the counting argument fails and the linear bound with it. **30-minute
test. Run first.**

**R3 — `Aux` parametrization lands on the K/T/B surface.** Phase 7 changes `ModalLoopInvGen`'s
shape. *Mitigation*: `extends` + the Phase 9 regression gate (K-facing name/statement unchanged).
*Kill*: if `modalExpandBranchesGen_hintikka` cannot be re-derived at `Aux := (∃ rank, …)`, the
factoring is wrong — **stop at Phase 9, before any S5-specific work is wasted.**

**R4 — Un-enumerated `modalApplyOneS5_snd_eq` consumers.** Run `lean_references` before Phase 11.
*Kill*: if a consumer genuinely needs the **unconditional** form and is load-bearing for the
countermodel half, the "ports free" claim is falsified. (I judge this unlikely — `hintikka_congr`
bypasses that lemma entirely — but it is INFERRED.)

**R5 — Correctness is validated, not proved.** 3963 formulas / 0 mismatches / 0 instability is
strong evidence, **not a proof**. Depth 2, two atoms.

**Falsifiers**: any formula with `maxWorld > modalOps φ` under `modalApplyOneS5w` breaks the counting
argument. Any super-linear world growth breaks it. (The **keyed** rule *does* grow quadratically —
⌊n²/4⌋+1 on alternating `□◇` chains — which is a further reason it is not the recommendation.)

**Fallback** (in order):
1. If R2 fails but the rule is sound: keep the rule, obtain the world bound another way. This is a
   phase, not a redesign.
2. If R1 fails: the **atom-quotient semantic FMP** route (`Decidable (s5Valid φ)` via enumerating
   quotient models over `Fin k → Bool`) is **pre-authorized** by plan 02 Phase 8's Blocked branch,
   and was compiled sorry-free and axiom-clean in this dossier. It delivers deliverable (4) only —
   not `modalTableauS5_complete`, and **not** 5/KB5 (its `qTransfer` needs reflexivity, which
   `fiveFC`/`kb5FC` lack). Legitimate as a documented `[PARTIAL]`, not as the primary route.

**Two scope corrections the plan must own before writing phases** (neither is caused by this
recommendation, both will otherwise silently appear as phases):

- **5/KB5 is not delivered, and no S5 tableau can deliver it.** `fiveFC := RightEuclidean` and
  `kb5FC := Symm ∧ RightEuclidean` (FrameSoundness.lean:1283/1291) are **strictly larger** frame
  classes than `s5FC := Refl ∧ RightEuclidean` (:1273); `□p → p` separates them. So
  `fiveValid ⊊ s5Valid` and the S5 tableau's two halves do not compose into a decision procedure for
  `fiveValid`. FrameCompleteness.lean:571-580's claim that 5/KB5 merely *"needs
  `modalTableauS5_complete` … as its proof engine"* is **wrong on mathematics, not scheduling**, and
  should be corrected as part of this task — it will otherwise mislead the next planner exactly as
  it appears to have misled the last one.
- **"against `Cube.S5`" is a docstring gesture, not a theorem.** No Lean theorem connects `s5Valid`
  to `Cube.S5` — and none connects `kValid` to `Cube.K` either, so this is precedent-consistent
  rather than an S5 regression. The real deliverable is `Decidable (s5Valid φ)`.

---

## 8. Rejected Alternatives

**Recorded so a future dispatch does not re-attempt a dead end — exactly as the rank measure was.**

1. **Fuel domination (R7).** *Rejected: false statement.* The unguarded expansion is unbounded
   (`maxWorld = fuel/2`) [VERIFIED]. No fuel dominates it. Do not spend another cycle here.

2. **Any firing-order / stratification / "create all worlds, then fire boxes" / fairness discipline.**
   *Rejected: provably impossible.* The divergence is a property of the rule set's **closure**, not
   its **schedule**. A **fair** schedule keeps firing the box at every known world, forcing
   `T(◇p)@w_max` onto the branch, which the fresh-minting arm answers with a new world — divergence.
   An **unfair** schedule that stops firing the box loses Hintikka conjunct 2. That dichotomy *is*
   the measured c2/c4 parity alternation. Stratification has **no fixed point** because *firing
   boxes creates world-creating formulas*: at `[T(□◇p)@0]` the mint stratum is empty until the box
   stratum runs, and the box stratum re-arms the mint stratum forever. **The strata do not
   stratify.** (This also pre-emptively kills the unevaluated Massacci π-before-ν ordering route.)

3. **Static pre-allocation (a-priori world set computed from φ₀).** *Rejected: type-level
   impossibility.* `modalExpMeasure_step_lt_gen`'s `hOutputsSubsetUniverse` binds `φ0`
   **universally inside the hypothesis** (FmpMeasure.lean:3241) [VERIFIED]. A φ₀-parametrized rule
   `modalApplyOneS5a φ₀` can never discharge `∀ φ0, …` — for `φ0 := ◇p₀` and a large `φ₀`, the rule
   emits a witness at a world outside `modalUniverse (◇p₀)`. Repairing it means reordering binders
   in the **shared** measure layer, falsifying the design's own headline claim ("generic driver
   untouched"). The witness rule is plain `RuleApply Atom` and discharges the field **uniformly**.
   *(This also explains why the landed `modalApplyOneS5g phi0` precedent never reached the measure
   layer.)*

4. **Keyed driver over `modalStepBranchS5gKeyed`.** *Rejected on cost, not correctness.* The keyed
   stepper genuinely saturates and decides S5 correctly (0/700 differential errors), and
   `blocked_witness_mem` compiles from `S5LoopInv.keyLowerBd`. But `modalExpMeasure_step_lt_gen` is
   stated for `modalStepBranchGen` [VERIFIED], so a keyed driver cannot consume the measure engine
   **or** `modalExpandBranchesGen_hintikka`, and must re-derive both. It also grows **quadratically**
   (⌊n²/4⌋+1 on `□◇` chains) and has an unresolved `keysTotal`-at-initialization gap (the driver
   starts `keys = []` while world 0 is already known). Its "~1,900 preserved lines" are inputs to
   work that must still be written from scratch.

5. **The unkeyed guard `modalApplyOneS5g` / `blockingWorldS5`.** *Rejected: structurally dead.*
   `blockingWorldS5 = none` at **every** mint decision point. The guard demands exact equality
   between a world's **current** relevant set and a prospective successor's **birth** content, but
   S5's universal box injects formulas **post-birth**, so every extant world's content strictly
   exceeds any birth content. The S4 birth-content abstraction is sound only because in S4 a world
   inherits at birth everything it will ever have. **S5 violates that premise.** This is the user's
   "mirroring S4 is wrong for S5" suspicion, mechanically confirmed at the exact point of failure.

6. **Keeping `modalUniverseS5`/`modalWorldBoundS5` (loose-but-sound).** *Rejected: breaks the fuel.*
   `entryWorkS5 > fuelExp` at `atom` (19 > 8), `□p` (135 > 120), `p∧q` (779 > 120) [VERIFIED]. The
   looseness sits **in the exponent** of the fuel comparison. And the proposed escape hatch
   `modalWorldBoundS5 φ ≤ modalWorldBound φ` is **false** [VERIFIED].

7. **`.linear []` on the reuse arm.** *Rejected*: breaks `freshLocal`'s right disjunct (needs a
   cons). The landed `modalApplyOneS5g` makes exactly this mistake (:987).

8. **A `hasEdge` guard on the reuse arm.** *Rejected*: makes `.notApplicable` reachable on a mint
   shape, inverting the `exfalso` conjunct-3/4 discharge (CompletenessLoop.lean:1049-1060) from a
   refutation into a proof obligation. Guard-less costs at most one duplicate edge per (formula,
   world) and is measure-inert.

9. **Filtration / FMP as the route to Phase 8.** *Rejected: category error.* Blackburn's Filtration
   Theorem is **purely semantic** — it quantifies over models, never over tableau branches — so it
   cannot produce `modalHintikkaSetGen`. Worse, the naive form is **false for S5**: filtration
   preserves reflexivity but **not** transitivity or symmetry (Blackburn2001 p.79-81 verbatim:
   *"transitivity and symmetry are obvious counterexamples"*), and Lemma 2.42's `R_t` is *"Left as
   Exercise 2.3.5"* — unproven in the source. A concrete counterexample exists: a smallest filtration
   of an S5 model that is reflexive and symmetric but **not transitive**.

10. **Doczkal-Smolka-style pruning.** *Rejected: no fixpoint.* DS pruning is a greatest fixpoint that
    needs the box condition to constrain only the **edge**. S5's universal relation makes it a
    **global** condition on the state set (`□ψ ∈ H ↔ ∀H'∈T. ψ∈H'`), so shrinking `T` makes boxes
    **easier** and diamonds **harder** simultaneously — neither monotone nor antitone. Nothing to
    iterate.

11. **Tightening `modalFuel`.** *Rejected as scope creep.* Sufficiency, not tightness, is the
    requirement, and `modalFuel` is reused **unchanged** at K's universe. Optional polish; do not put
    it on the critical path.

---

## 9. References

### In `references.bib` — READ (primary source obtained and quoted)

- **Gore1999** — Goré, *Tableau Methods for Modal and Temporal Logics*, Handbook of Tableau Methods,
  Kluwer. `references.bib:987`.
  **PDF obtained** at `https://www.inf.ufpr.br/marcos/ci311/Gore_Tableau_methods_for_modal_and_temporal_logics.pdf`
  (= ANU Automated Reasoning Project **TR-ARP-15-95**, RSISE, May 5 1995, rev. Sep 12 1997 — the
  complete draft of the Handbook chapter). The ANU original is dead; **this mirror works**.
  > **CITE BY TR PAGINATION** (TR pp.1-106), **NOT** the Handbook's pp.297-396. They do not map.
  - TR p.48 — the bug, predicted: a static rule that is not "once off" *"can lead to an infinite
    chain A ∈ w, ◇A ∈ w, ◇◇A ∈ w, ... so this system cannot give a decision procedure for S5
    either."*
  - TR pp.44-45 — the linear model graph: one successor per `¬□Qᵢ ∈ w₀`, level one, *"and stop!"*,
    `R` = reflexive/transitive/symmetric closure of `≺`, `|W| = 1 + m`.
  - TR p.85 — *"we do not mark ν-formulae as finished since they may need to be used again and
    again."*
  - TR pp.79-80, 97-99 — labels eliminate the analytic cut S5 needs in implicit systems; LC*K45 is
    cut-free, labels of length ≤ 2, and *"we do not need any check for periodicity."*

- **Blackburn2001** — Blackburn, de Rijke & Venema, *Modal Logic*, CUP. `references.bib:65`.
  Corpus on disk: `/home/benjamin/Projects/Literature/sources/blackburn_2002/`.
  > **Note**: the FTS index is degraded and the chunks are binary-detected — plain `grep` silently
  > returns nothing. **Use `grep -a`.**
  - §6.6 p.382 — the `m+1` selection-of-points bound for S5 and its NP-completeness (quoted §2.2).
  - Ex. 6.6.4 — *"Use a selection of points argument to show that S5 has the polysize model
    property, and is NP-complete."* **Left as an exercise — attests the architecture, not
    formalizable as-is.**
  - §2.3 Def 2.36 / Thm 2.39 / pp.79-81 / Lemma 2.42 — filtration and its failure to preserve
    transitivity/symmetry (§8 item 9).

- **Fitting1983** — `references.bib`. **NOT obtained** (1983 Reidel book; no PDF located). Every
  claim about Fitting's prefixed tableaux here is **SECONDARY**, via Gore's citations. Gore's own
  systematic construction is credited to [Fit83 p.402] (gore.txt:3689-3692) — that one page
  reference is corroborated; the others are not verified.

- **Massacci2000** — `references.bib:974`. **NOT obtained** (paywalled). Gore (TR p.85) notes
  Massacci gives an alternative systematic procedure processing all `σ::¬□P` **before** all
  `σ::□Q` — a π-before-ν **ordering** discipline. **Rejected** by §8 item 2's dichotomy, but the
  primary source was never read.

- **ChagrovZakharyaschev1997** — `references.bib`. **NOT obtained**, and **nothing in this report
  depends on it.**

### Not in `references.bib` — full data given, use only if cited

- **Caridroit, Lagniez, Le Berre, de Lima, Montmirail**, *"A SAT-based approach for solving the modal
  logic S5-satisfiability problem"*, AAAI-17, pp. 3864-3870. **READ** —
  `http://www.cril.univ-artois.fr/~caridroit/downloads/S5SATP_aaai_2017.pdf` (WebFetch fails on the
  compressed PDF; extract with `pdftotext`). Tableau **condition 7** — *"if ◇ψ₁ ∈ s then ∃s' ∈ T
  s.t. ψ₁ ∈ s'"* — is an **existential over the whole tableau**, i.e. **exactly the reuse test**, not
  a fresh mint. **Lemma 2**'s `g(ψ)` charging argument is the syntactic analogue of Phase 5's
  counting proof. *Optional*: Gore1999 alone suffices for BibKey traceability.
- **Halpern & Rêgo**, *"Characterizing the NP-PSPACE Gap in the Satisfiability Problem for Modal
  Logic"*, J. Logic and Computation 17(4):795-806, 2007; arXiv cs/0603019. **READ** —
  `https://www.cs.cornell.edu/info/people/halpern/papers/complexity.pdf`. Theorem 3.1 is a complete,
  open-access proof of the S5 selection theorem. **Semantic**, so it supports the bound but is not
  the tableau termination argument.
- **Ladner 1977** — **NOT obtained.** The `ladner1977.pdf` in the session scratchpad is a **919-byte
  HTML error page**, not a PDF. **Do not cite it.** The NP-completeness claim is fully covered by
  Blackburn2001 §6.6 (in-bib, on disk).
- **Open Logic Project**, *Normal Modal Logic: Filtrations and Decidability* / *Frame Definability:
  Equivalence Relations and S5*, rev. 9620cc7 (2026-07-12), CC-BY,
  `https://builds.openlogicproject.org/`. **READ.** Every OLP claim relied on here is independently
  corroborated by Blackburn2001 or Gore1999 — **except §fil.9** (pure-euclidean filtration failure),
  which is the sole citation for FrameCompleteness.lean:571-580's out-of-scope note and independently
  confirms that gap is a **real mathematical obstruction**, not a local shortcut.
  > **Correction to the record**: OLP Thm fil.17 is a **dovetailing** argument with **unbounded**
  > model size relying on proof-system completeness. It gives **no bound** and must not be cited for
  > one.

### Mechanized this session (`lean_run_code`, no file edited)

| Result | Status |
|---|---|
| `modalOps_lt_worldBound` | **PROVED** sorry-free, `[propext, Classical.choice, Quot.sound]` |
| `hintikka_congr` | **PROVED** sorry-free, `[propext]` |
| `modalApplyOneS5w_boxPos_eq` / `_diaNeg_eq` | **PROVED** by `rfl`, `[propext]` |
| `witnessWorldS5_mem` | **PROVED** sorry-free, `[propext, Quot.sound]` |
| `diaPosWitness'` (F12′, guard-less) | **PROVED** sorry-free, `[propext, Quot.sound]` |
| Shipped-driver divergence (`maxWorld = fuel/2`) | **VERIFIED** by execution |
| `entryWorkS5 > fuelExp` at `atom`/`□p`/`p∧q` | **VERIFIED** by execution |
| `modalWorldBoundS5 ≰ modalWorldBound` | **VERIFIED** by execution |
| Witness rule: 3963 formulas vs exact oracle | **0** mismatches / **0** unstable / **0** bound violations |
| Witness rule saturates `□◇p` at 2 worlds, fuel 20→2000 | **VERIFIED** by execution |
