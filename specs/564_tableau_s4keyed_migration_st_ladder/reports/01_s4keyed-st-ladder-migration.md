# Research Report: S4 Keyed / KeyedOrdered Migration onto the RuleApplySt / St Ladder

**Task**: 564 — migrate the S4 Keyed and KeyedOrdered drivers onto the `RuleApplySt` / St ladder,
retire the duplicated `keys'` re-derivation, and decide the fate of `S4LoopInv.outDegEq`.

**Status**: researched. Every structural claim below was verified against the live tree; the
migration bridge was verified by *compiling it* (see "Compiled Evidence"), not by reasoning.

---

## 0. Verified baseline (re-measured, not inherited)

| Gate | Command | Result |
|------|---------|--------|
| Build | `lake build Cslib` | **green**, exit 0 |
| Sorry census, `Modal/Tableau` | `grep -rn "^\s*sorry\s*$\|:= sorry\|<;> sorry\|exact sorry" Cslib/Logics/Modal/Tableau/` | **exactly 1** — `FrameSoundness.lean:1251` |
| HEAD | `git log --oneline -1` | `9a3b2370` |

Import reachability confirmed: `LoopChecking → FmpMeasure → Saturation`, so `RuleApplySt`,
`modalStepBranchGenSt`, `modalExpandBranchesGenSt`, `modalTableauGenSt` are **already in scope**
in `LoopChecking.lean` with no import change required.

---

## 1. Corrections to the task description

The description warns its own line numbers may be stale. They are. Anchor on names:

| Description claim | Actual |
|---|---|
| stepper re-derives at `LoopChecking.lean:951-953` | `modalStepBranchS4Keyed`, **LoopChecking.lean:1298-1308** (and a *second* copy in `modalStepBranchS4KeyedBody`, **:1348-1358**) |
| `outDegEq` preservation at `:4917-5105` and `:5111-5307` | `modalStepBranchS4_preserves_outDegEq` **:5473-5672 (200 lines)**; `modalStepBranchS4KeyedOrdered_preserves_outDegEq` **:5674-5874 (201 lines)** |
| second ordered variant is "undocumented" | **False** — it carries a 5-line docstring at `:5674-5678` |
| provision sites `:7569`, `:7633`, `FrameCompleteness:4217-4218` | **`LoopChecking:8179`, `LoopChecking:8244`, `FrameCompleteness:4132`** (the positional `refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_, ?_, ?_⟩, …⟩`) |
| "four other invariant proofs that destructure the structure" | **Two**, both in `LoopChecking.lean`: `:8163` and `:8225`, each the identical `obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩ := hinv` |
| `S4LoopInv.outDegEq` field | **`LoopChecking.lean:7690`** |

Also worth recording: `S4LoopInv` is only ever *constructed* by named-field `exact { … }` syntax
(`:8168`, `:8233`) except at the single positional site in `FrameCompleteness.lean:4132`. That
one site is the only place field *arity* matters.

---

## 2. Compiled Evidence — the Keyed migration bridge WORKS

A complete, sorry-free bridge chain was written and **compiled clean** with
`lake env lean` against the live tree. It is preserved verbatim at:

`/home/benjamin/Projects/cslib/specs/564_tableau_s4keyed_migration_st_ladder/assets/verified-st-bridge.lean`

It contains, all green:

1. **`modalApplyOneS4KeyedSt φ₀ : RuleApplySt Atom (List (WorldIndex × Finset (Sign × Proposition Atom)))`**
   — the state-threaded keyed rule. It makes the `blockingWorldS4Keyed` decision **exactly
   once**, returning `(result, newAcc, keys')` from a single `match`. ~18 lines.
2. **`modalApplyOneS4KeyedSt_proj`** — projects onto `modalApplyOneS4Keyed φ₀ keys`.
   Proof is 3 tactic lines (`unfold`; `rcases sf`; `cases s <;> cases f <;> simp_all <;> (try split) <;> simp_all`).
3. **`modalApplyOneS4KeyedSt_eq`** — the state-threaded rule is *componentwise* the stateless
   rule paired with the stepper's own `keys'` expression. Proof is 3 tactic lines
   (`cases s <;> cases f <;> dsimp only <;> (split <;> rename_i h <;> simp only [h])`).
4. **`modalStepBranchGenSt_eq_S4Keyed`** — `modalStepBranchGenSt (modalApplyOneS4KeyedSt φ₀) b e acc keys = modalStepBranchS4Keyed φ₀ b e acc keys`.
   Proof is 7 tactic lines, closing via `congr 1; funext sf; by_cases hexp; rw [modalApplyOneS4KeyedSt_eq]; rfl`.
5. **`modalExpandBranchesGenSt_eq_S4Keyed`** — the whole loop, at any fuel.
   Proof is ~45 lines: fuel induction with a `suffices key : ∀ pending …` inner induction on
   `pending`, structurally mirroring the landed `modalExpandBranchesGen_eq_St`
   (`Saturation.lean:677`). **The mirror is exact** — the same `processNext`-shaped induction
   works because `modalExpandBranchesS4Keyed.processNext` and
   `modalExpandBranchesGenSt.processNext` are declaration-for-declaration identical.

Tactic hazards found and already solved in the asset (do not re-derive these):
- After `cases s <;> cases f` the `{sign := …}.sign` projections must be discharged with a bare
  `dsimp only` **before** `split`, or `split` targets the wrong `match` and `rfl` fails with a
  cross-arm mismatch (observed: the `Sign.neg, □φ` arm being offered for a `.pos, ◇` formula).
- In `modalStepBranchGenSt_eq_S4Keyed`, use `rw [modalApplyOneS4KeyedSt_eq]` and **not**
  `simp only [modalApplyOneS4KeyedSt_eq]`: `simp` normalises `branches.map (fun _ => e ++ [sf])`
  into `List.replicate branches.length (e ++ [sf])` on one side only, and the goal then will not
  close. `rw` followed by a bare `rfl` closes it.
- The `fuel = 0` base case needs a trailing `rfl` after `simp only [modalExpandBranchesGenSt, modalExpandBranchesS4Keyed]`.

---

## 3. STRUCTURAL BLOCKER — the KeyedOrdered driver CANNOT be migrated onto this ladder

`modalStepBranchGenSt` (`Saturation.lean:552`) hardwires the traversal:

```
b.findSome? fun sf => if expanded.any (· == sf) then none else … apply sf b acc st …
```

It abstracts over the **rule**, not the **traversal**. `modalStepBranchS4KeyedOrdered`
(`LoopChecking.lean:1439`) is a *two-stage* traversal:

```
match (modalNonMintCandidates φ₀ keys b e acc).findSome? (modalStepBranchS4KeyedBody …) with
| some r => some r
| none   => modalStepBranchS4Keyed φ₀ b e acc keys
```

This is **not** `b.findSome? f` for any per-element `f`. Whether a minting-shaped `sf` is allowed
to fire depends on whether *any other* formula anywhere on `b` is a live non-minting candidate —
a global property of `b`, not a function of `sf`. Therefore no choice of `apply : RuleApplySt Atom σ`
makes `modalStepBranchGenSt apply` compute `modalStepBranchS4KeyedOrdered`, and by extension
`modalExpandBranchesS4KeyedOrdered` cannot be expressed as `modalExpandBranchesGenSt apply`.

**Consequence for scope**: the task's stated scope ("migrate the S4 Keyed **and** KeyedOrdered
drivers") is only half-achievable against the ladder as it stands. Migrating the ordered driver
requires a *new rung* in `Saturation.lean` parameterised by a stepper
(`step : List SF → List SF → Accessibility → σ → Option (… × σ)`) rather than a rule — a
different and larger generalisation than the one that landed. Recommend the plan either scope
the ordered driver out explicitly, or budget the new rung as its own phase.

---

## 4. SECONDARY BLOCKER — `modalTableauGenSt` hardwires K's fuel

`Saturation.lean:741`:

```lean
modalExpandBranchesGenSt apply [initialBranch] [[]] [Accessibility.empty] [st0] (modalFuel φ)
```

`modalTableauS4Keyed` uses `modalFuelS4 φ` (`LoopChecking.lean:417`), which is *not* `modalFuel φ`
— the module docstring records that K's `modalFuel` is confirmed **not** provably sufficient for
the S4 keyed loop's pigeonhole world bound. So `modalTableauGenSt` cannot express the S4 entry
point.

**Fix, no Saturation change needed**: point the entry point at `modalExpandBranchesGenSt`
*directly* (it takes fuel as an argument):

```lean
def modalTableauS4Keyed (φ : Proposition Atom) : ModalTableauResult Atom :=
  modalExpandBranchesGenSt (modalApplyOneS4KeyedSt φ) [[⟨.neg, φ, 0⟩]] [[]]
    [Accessibility.empty] [[(0, (∅ : Finset (Sign × Proposition Atom)))]] (modalFuelS4 φ)
```

Do **not** add a fuel parameter to `modalTableauGenSt`; that would touch the landed
`modalTableauGen_eq_St` bridge for zero benefit.

---

## 5. THE PREMISE IS FALSIFIED — there is no line-count reduction in retiring the double derivation

The task description asserts: *"Retiring that double derivation is where the unquantified
line-count reduction actually lives."* Measurement says otherwise.

**What the double derivation actually costs**: 11 lines in `modalStepBranchS4Keyed` (`:1298-1308`)
plus 11 lines in `modalStepBranchS4KeyedBody` (`:1348-1358`) = **22 lines of definition**.

**What retiring it costs**: the bridge chain in §2 is **~100 lines** (18 def + ~80 proof), all of
which is *new*.

**Why the deletion does not compound into the proofs**: 40 downstream proof sites depend on the
*definitional shape* of the steppers:

| Anchor | Sites |
|---|---|
| `unfold modalStepBranchS4Keyed` | **21** (19 in `LoopChecking.lean`, 2 in `FrameCompleteness.lean:7627,7904`) |
| `unfold modalStepBranchS4KeyedBody` | **19** in `LoopChecking.lean` |
| `simp`/`unfold` on `modalExpandBranchesS4Keyed{,Ordered}{,.processNext}` | **8** (`LoopChecking:11301,11304,11330,11646,11670,11690`; `FrameCompleteness:8092,8144`) |
| `unfold modalApplyOneS4Keyed` | **14** |

Each of the 21 `unfold modalStepBranchS4Keyed at h` sites is followed by
`List.exists_of_findSome?_eq_some`, `split_ifs`, `rcases hpair : modalApplyOneS4Keyed φ₀ keys sf b acc`,
then a 14-leaf `rcases hs : sf.sign <;> rcases hf : sf.formula` split. That case split is required
**regardless** of whether `keys'` is re-derived — `modalApplyOneS4Keyed` itself matches on
`sf.sign, sf.formula`, so the state-threaded rule needs the identical split to pin `result`. The
re-derivation adds **no** proof leaves; the existing helpers
`modalStepBranchS4Keyed_result_keys_eq` (`:2936`) and `_result_acc_eq` (`:2963`) already extract
the 4th and 3rd tuple components result-shape-agnostically in 5 tactic lines each.

**Net accounting of a destructive redefinition** (redefine the bespoke names as the generic ones):

| Item | Δ lines |
|---|---|
| add `modalApplyOneS4KeyedSt` + 3 bridge theorems | **+100** |
| `modalStepBranchS4Keyed` body → one-liner | −20 |
| `modalStepBranchS4Keyed` old body re-stated so 21 `unfold` sites keep working | **+20** (it just moves into a lemma statement) |
| `modalExpandBranchesS4Keyed` body → one-liner | −49 |
| `keys'` match deleted from `modalStepBranchS4KeyedBody` | −10 |
| 40 tactic-script edits (`unfold X` → `rw [X_eq]; unfold Body`) | ~+40 |
| **Net** | **≈ +80 lines, plus re-verification of 40 proof sites** |

**Conclusion**: the migration is architecturally worthwhile (it gives the landed St ladder its
first real consumer and discharges the "separate, later task" note at `Saturation.lean:502-505`),
but it is line-count **negative**. Do not plan it as a reduction.

---

## 6. `S4LoopInv.outDegEq` — VERDICT: REMOVE. The cascade is 6 mechanical sites.

The description's escape hatch ("if the cascade … is large, KEEP the field") does not trigger.
The cascade was fully enumerated:

**Consumers of the field: ZERO.** No `.outDegEq` projection exists anywhere in `Cslib/`. The
only bindings are `hoD` at `:8163` and `:8225`, each used solely to feed the field back at
`:8180` / `:8245`. (`ModalPotentialInv.outDegEq` in `FmpMeasure.lean:2259` is a **different**
structure and is out of scope — do not touch it, and do not touch
`modalStepBranch_preserves_outDegEq{,_gen}` in `FmpMeasure.lean` or
`modalStepBranchGen_preserves_outDegEq` in `GenericDriver.lean`, all of which serve K.)

**Deletions** (exact ranges, verified by boundary walk):

| Declaration | Range | Lines |
|---|---|---|
| `modalApplyOneS4KeyedMint_outDeg_step` (incl. `omit` + docstring) | `LoopChecking.lean:1017-1042` | 26 |
| `modalStepBranchS4_preserves_outDegEq` (incl. docstring) | `LoopChecking.lean:5473-5672` | 200 |
| `modalStepBranchS4KeyedOrdered_preserves_outDegEq` (incl. docstring) | `LoopChecking.lean:5674-5874` | 201 |
| **subtotal** | | **427** |

`modalApplyOneS4KeyedMint_outDeg_step` is orphaned by the removal: its only four call sites
(`:5516`, `:5583`, `:5718`, `:5785`) are all inside the two doomed lemmas. It is safe to delete
and was **not** anticipated in the task description.

**Edits** (6 sites, all mechanical):

1. `LoopChecking.lean:7689-7690` — delete the `outDegEq` field and its docstring line.
2. `LoopChecking.lean:8163` — `obtain ⟨hbC, heN, heC, haF, haK, hoD, hkT, hkL, hkD, hkI⟩` →
   drop `hoD` (9-way).
3. `LoopChecking.lean:8179-8180` — delete the `outDegEq := …` field assignment (2 lines).
4. `LoopChecking.lean:8225` — same `obtain` edit as (2).
5. `LoopChecking.lean:8244-8245` — delete the `outDegEq := …` field assignment (2 lines).
6. `FrameCompleteness.lean:4132` — drop the **6th** slot (the 4th `?_`) from
   `refine ⟨⟨?_, List.nodup_nil, ?_, accFreshInv_empty _, ?_, ?_, ?_, ?_, ?_, ?_⟩, …⟩`, and
   delete the matching bullet, which is unambiguously identifiable by its body:
   ```
   · intro w
     simp [outDeg, Accessibility.successorsOf, Accessibility.empty]
   ```

Also update the four docstrings that enumerate the field list: `LoopChecking.lean:4644`, `:7667`,
`:8148`, `:8196` (each lists `outDegEq` in a `bClosure/eNodup/eClosure/accFresh/accKnown/outDegEq`
run). These are prose-only; missing one is a doc defect, not a build break.

**Total reduction: ~437 lines.** This is where *all* the task's line-count reduction lives.

**Residual risk**: after deletion, `isMintingShaped` and `outDeg` have no remaining use inside
`LoopChecking.lean`. Both are declared in `FmpMeasure.lean`, which `LoopChecking` imports for
dozens of other reasons, so no import can be dropped and `lake shake` should be unaffected.
Verify against the shake gate anyway (below).

---

## 7. Recommended phasing

The two halves are **independent** — different declarations, no shared anchors. Sequence them so
a failure in one does not strand the other.

**Phase A (do first — the whole payoff, low risk): remove `outDegEq`.**
Six edits + three deletions, all enumerated in §6. Expect `lake build Cslib` green with no
proof-script authoring at all. −437 lines.

**Phase B (additive, zero risk): land the St bridge.**
Copy the four declarations from
`specs/564_tableau_s4keyed_migration_st_ladder/assets/verified-st-bridge.lean` into
`LoopChecking.lean`, placed after `modalExpandBranchesS4Keyed`. Do **not** redefine any existing
declaration. Docstrings must be authored (docBlame); `modalApplyOneS4KeyedSt` will need a
`@[nolint unusedArguments]`-style review only if the linter flags it (it should not — `Atom`
appears in `RuleApplySt`'s explicit args here, unlike the `abbrev` case). Update
`Saturation.lean:502-505`'s "separate, later task, out of scope here" note to point at the landed
bridge. +~100 lines.

**Phase C (optional, needs explicit user sign-off): redefine the bespoke drivers.**
Only if the user wants the bespoke definitions actually retired rather than bridged. §5 shows
this is net **+80 lines and 40 proof sites re-verified**. Recommend **not** doing this. If the
plan includes it anyway, it must be its own phase with an explicit revert point, and it must
touch `modalStepBranchS4Keyed` before `modalExpandBranchesS4Keyed` (the latter's bridge consumes
the former's).

**Out of scope, flag as such**: the KeyedOrdered driver (§3). Migrating it needs a new
stepper-parameterised rung in `Saturation.lean`. That rung *would* let
`modalExpandBranchesS4Keyed` (50 lines) and `modalExpandBranchesS4KeyedOrdered` (50 lines)
collapse into two one-line instantiations — but the rung itself is ~55 lines plus two ~50-line
bridge proofs, so it is again roughly net-zero. Recommend spawning it as its own task if the
architectural consolidation is wanted for its own sake.

---

## 8. Verification gates for the implementer

Per the established baseline, gate on:

```bash
lake build Cslib                                        # must be green
grep -rn "^\s*sorry\s*$\|:= sorry\|<;> sorry\|exact sorry" Cslib/Logics/Modal/Tableau/   # must stay exactly 1
lake exe checkInitImports                               # exit 0
lake exe lint-style                                     # exit 0
lake shake --add-public --keep-implied --keep-prefix    # exit 1 with 9 findings, NONE in Modal/Tableau
```

`lake shake` gate is **"no Modal/Tableau findings AND count stays 9"** — do **not** gate on exit 0.

Zero-debt: no `sorry` may be introduced. Nothing in §6 or §7-Phase-B requires one — Phase A is
pure deletion of already-proved material, and every Phase B proof is already compiled in the
asset file.

---

## 9. Reuse check (CSLib reuse-first)

Ran before recommending any new declaration:

- `Cslib/Logics/Modal/Tableau/Support/Accessibility.lean` and `Support/KnownWorlds.lean` exist and
  are imported by `LoopChecking.lean` (lines 19-20). No fact from them is restated in this plan.
- A `Support/Subfmls.lean` was previously evaluated and rejected; nothing here revives it.
- No new abstraction is proposed. `modalApplyOneS4KeyedSt` is an *instantiation* of the existing
  `RuleApplySt` (`Saturation.lean:521`) at `σ := List (WorldIndex × Finset (Sign × Proposition Atom))`
  — precisely the instantiation `RuleApplySt`'s own docstring names as intended (`:512-514`).
- No new notation. No new typeclass.
