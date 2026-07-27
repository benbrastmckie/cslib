# Research: Discharge `nested_sound_impL` via the Source's Λ-Chain Induction

**Task**: 570 — `nested_sound_impL_lambda_chain_induction`
**Task type**: cslib (lean4) | **Effort**: `--hard` | **Reference grounding tier**: **Tier 1 (literature-backed)**
**Session**: `sess_1785113705_bcf38a`
**Report**: `/home/benjamin/Projects/cslib/specs/570_nested_sound_impL_lambda_chain_induction/reports/01_lambda-chain-induction.md`

---

## Executive Summary

The Λ-chain induction the task asks for **is real, is small, and is now proved**. It is a
three-case structural recursion that took three lines once the missing ingredient was identified.
I proved it sorry-free during research (`lean_run_code`, zero diagnostics).

But discharging the sorry at `Soundness.lean:1315` is **blocked by two pre-existing defects that
must be fixed first**, both established with Lean-verified evidence:

1. **`lemma4_7_ii` does not exist.** The file's module docstring claims Lemma 4.7(i) and (ii)
   "display literally the same visible formula" and lands **one** Lean fact (`lemma4_7_i_ii`) for
   both citations. That claim is **false**. A direct `pdftotext -layout` render of page 10 shows
   (i) and (ii) are different statements. `lemma4_7_i_ii` is Lemma 4.7(i) only. Lemma 4.7(ii) —
   the ingredient the source explicitly names for *this very induction* — was never landed. This
   is exactly why the Λ-chain induction "does not reduce to 4.4/4.5/4.8 alone".
2. **`InputCtx.outputPruning` is off by one nesting level when `ctx.Λ = []`**, which makes
   `nested_sound_impL` **false as currently stated**, not merely unproved. Counterexample below.

Additionally, **the baseline is not green**: `lake build` of the target module currently FAILS
(`nested_sound` is non-exhaustive — the `NestedProof.cut` case is missing). This is committed
state on a clean tree, not something this task introduced.

With defects (1) and (2) repaired, I assembled the **complete, sorry-free discharge of `⊃•`** in
Lean during research. The path is fully de-risked; the plan is now an editing task, not a
discovery task.

---

## Baseline (Required Metrics)

| Metric | Value | How measured |
|--------|-------|--------------|
| Cslib sorry census | **41** | `bash .claude/scripts/lean-sorry-census.sh Cslib` → `sorry_count: 41` |
| Target sorry, listed once | `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1315` | same census inventory |
| `lake build` (module) | **RED — FAILS** | `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness` |
| Build error | `Soundness.lean:1329:2: Missing cases: _, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)` | same |
| Sorry warning | `Soundness.lean:1306:8: declaration uses 'sorry'` | same |
| Working tree | clean for `Cslib/` (`git status --short Cslib/` empty) | `git status` |
| Last touching commit | `88b198bf` "task 554 phase 13.1: … assemble nested_sound with impL strategic sorry" | `git log` |
| `lake test` | **not run** — the library does not build, so a test run would be uninformative | — |

**Exit criterion for the plan**: census `sorry_count` must go `41 → 40`, the `Soundness.lean:1315`
entry must disappear from the inventory, **and** `lake build` must go RED → green (which requires
discharging `cut` too — see Finding 3).

---

## Source-to-Implementation Mapping (H3, Tier 1)

**Source**: R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
Logics*, LMCS 11(3:7), 2015.
**BibKey**: `ArisakaDasStrassburger2015` — **VERIFIED** at `references.bib:939`.
**Local corpus**: `~/Projects/Literature/sources/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics/`
(`source.pdf`, `chunk_0022.md`, `chunk_0023.md`).

| Source | Prop/Location | Lean Identifier | Type Signature | Status |
|--------|---------------|-----------------|----------------|--------|
| Arisaka–Das–Straßburger 2015 | Lemma 4.7(i), p. 10 | `Cslib.Logic.Modal.lemma4_7_i_ii` | `⊢ (A ∧ B) ⊃ C → ⊢ ((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)` | transcribed (**mislabelled**: covers (i) only) |
| Arisaka–Das–Straßburger 2015 | **Lemma 4.7(ii), p. 10** | `Cslib.Logic.Modal.lemma4_7_ii` | `⊢ (A ∧ B) ⊃ C → ⊢ ((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)` | **MISSING — proved in this research, needs landing** |
| Arisaka–Das–Straßburger 2015 | Lemma 4.7(iii), p. 10 | `Cslib.Logic.Modal.lemma4_7_iii` | `⊢ (A ∧ B) ⊃ C → ⊢ (□A ∧ □B) ⊃ □C` | transcribed |
| Arisaka–Das–Straßburger 2015 | Lemma 4.7(iv), p. 10 | `Cslib.Logic.Modal.lemma4_7_iv` | `⊢ (A ∧ B) ⊃ C → ⊢ (□A ∧ ◇B) ⊃ ◇C` | transcribed |
| Arisaka–Das–Straßburger 2015 | Lemma 4.8, p. 10 | `Cslib.Logic.Modal.lemma4_8` | `… → ∀ Γ, ⊢ (fm(Γ{Δ₁}) ∧ fm(Γ{Δ₂})) ⊃ fm(Γ{Σ})` | transcribed (`fillFull` flavour) |
| Arisaka–Das–Straßburger 2015 | Lemma 4.9 (`∧°`,`∨•`), p. 10 | `lemma4_9_fillRhs`, `lemma4_9_andR` | `… → ∀ ctx, ⊢ (fm(ctx{Ψ₁}) ∧ fm(ctx{Ψ₂})) ⊃ fm(ctx{Θ})` | transcribed (`fillRhs` flavour) |
| Arisaka–Das–Straßburger 2015 | **Lemma 4.9 (`⊃•`), p. 10, the `(L_X ∧ L_Z) ⊃ L_Y` induction on `n`** | `lambdaChain_XZ_imp_Y` | `∀ Λ, ⊢ ((Λ.fillRhs A°).fm ∧ (Λ.fillLhs (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm` | **proved in research, needs landing** |
| Arisaka–Das–Straßburger 2015 | Lemma 4.9 (`⊃•`), p. 10, "`(L_X ∧ (L_Y ⊃ P)) ⊃ (L_Z ⊃ P)` follows from `(L_X ∧ L_Z) ⊃ L_Y`" | `lambdaChain_step2` | `⊢ (X ∧ Z) ⊃ Y → ⊢ (X ∧ (Y ⊃ P)) ⊃ (Z ⊃ P)` | **proved in research, needs landing** |
| Arisaka–Das–Straßburger 2015 | Theorem 4.1 (`⊃•` case), p. 9–10 | `Cslib.Logic.Modal.nested_sound_impL` | `… hA → hB → Derivable (ctx.fillLhs (A⊃B)•).fm` | **sorry** (`Soundness.lean:1315`) — **and refutable as stated**, see Finding 2 |
| Arisaka–Das–Straßburger 2015 | Lemma 4.9 (`cut`), p. 10, "we additionally observe that `A ⊃ A` is always provable" | `nested_sound_cut` | `… → Derivable ctx.fillEmpty.fm` | **absent — blocks the build** (Finding 3) |
| Arisaka–Das–Straßburger 2015 | Observation 2.2 / Definition 2.3, p. 5 | `Cslib.Logic.Modal.InputCtx.outputPruning` | `InputCtx Atom → OutputCtx Atom` | **defective at `Λ = []`** (Finding 2) |

### Verbatim source text (page 10), the `⊃•` case

Rendered directly from `source.pdf` via `pdftotext -layout -f 10 -l 10`. Note that this PDF's
font encoding **drops the `□` glyph** (already documented in the module docstring); `∧`, `⊃`, `♦`
render correctly.

```
                            Γ′ {Λ{A◦ }}         Γ′ {Λ{B • }, Π◦ }
                         ⊃• −−−−−−−−−′−−−−−−−−−−−−−•−−−−−−−−−−−−−
                                   Γ {Λ{A ⊃ B }, Π◦ }
where Γ′ { }, Λ{ }, and Π{ } are output contexts. In particular, let
                         Λ{ } = Λ0 , [Λ1 , [. . . , [Λn , { }] . . .] ]   .
Now let P = fm(Π◦ ) and L_i = fm(Λi ) for i = 0 . . . n, and let
    LX = fm(Λ{A◦ }) = L0 ⊃ (L1 ⊃ (L2 ⊃ (· · · ⊃ (Ln ⊃ A) · · · )))          [□s dropped by pdftotext]
    LY = fm(Λ{B • }) = L0 ∧ ♦(L1 ∧ ♦(L2 ∧ ♦(· · · ∧ ♦(Ln ∧ B) · · · )))
    LZ = fm(Λ{A ⊃ B • }) = L0 ∧ ♦(L1 ∧ ♦(L2 ∧ ♦(· · · ∧ ♦(Ln ∧ (A ⊃ B)) · · · )))
To be able to apply Lemma 4.8, we need to show that (LX ∧ (LY ⊃ P )) ⊃ (LZ ⊃ P ) is
provable in HCK + X. But this follows from (LX ∧ LZ ) ⊃ LY , which can be shown provable
in HCK + X using an induction on n together with Lemma 4.7.(ii) and (iv). For the cut-rule
we additionally observe that A ⊃ A is always provable.
```

The dropped `□`s are recoverable, and I **Lean-verified** the recovery rather than guessing: the
Lean encoding computes `L_X` as `L₀ ⊃ □(L₁ ⊃ □(… ⊃ □(Lₙ ⊃ A)…))`. Confirmed by `rfl`:

```lean
example (A C L P : Proposition Atom) :
    ((ctxOk C L P).outputPruning.fillRhs (.atom A)).fm = C.imp (Proposition.box (L.imp A)) := rfl
```

`L_Y` and `L_Z` need no recovery and match `OutputCtx.fillLhs`'s `fm` exactly (also `rfl`-verified).

---

## Exact Statement and Shapes at the Sorry

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1306–1315`:

```lean
theorem nested_sound_impL (ctx : InputCtx Atom) (A B : Proposition Atom)
    (hA : Derivable (@CS5ModalAxiom Atom) (ctx.outputPruning.fillRhs (.atom A)).fm)
    (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (A.imp B))).fm := by
  sorry
```

The goal state is the bare `Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (A.imp B))).fm`
with `hA`, `hB` in context — there is no intermediate proof state to report, because no tactic has
been applied. What matters is the **unfolded shape** of the three `fm`s. From `Context.lean`
(`InputCtx.fillLhs`, `InputCtx.outputPruning`, `OutputCtx.fillRhs/fillLhs`, `buildRhsChain`) and
`Syntax.lean` (`fm`), writing `Γ' = ctx.Γ'`, `Λ = ctx.Λ`, `P = ctx.π.fm`, `Lᵢ = Λᵢ.fm`:

| | Lean term | `fm` |
|---|---|---|
| `hA` | `(Γ' ++ Λ).fillRhs (.atom A)` | `fm(Γ'{…})` with the hole filled by `L₀ ⊃ □(L₁ ⊃ □(… ⊃ □(Lₙ ⊃ A)…))` = `L_X` |
| `hB` | `Γ'.fillRhs (.box (Λ.fillLhs (.atom B)) π)` | `fm(Γ'{…})` with the hole filled by `□(L_Y ⊃ P)`, `L_Y = L₀ ∧ ◇(L₁ ∧ ◇(… ∧ ◇(Lₙ ∧ B)…))` |
| goal | `Γ'.fillRhs (.box (Λ.fillLhs (.atom (A.imp B))) π)` | as `hB` with `L_Z = L₀ ∧ ◇(… ∧ ◇(Lₙ ∧ (A⊃B))…)` in place of `L_Y` |

`ctx.outputPruning.fillRhs` is thus **output-polarity** (`□`/`⊃` chain, from `buildRhsChain`)
while `ctx.fillLhs` is **input-polarity** (`◇`/`∧` chain, from `OutputCtx.fillLhs`). That polarity
split is correct and is exactly the `L_X` vs `L_Y`/`L_Z` distinction. All shapes above were
confirmed by `rfl` in `lean_run_code` (six examples, zero diagnostics).

---

## Finding 1 (defect): Lemma 4.7(ii) Was Never Landed; the Docstring's "Duplication" Claim Is Wrong

**Counterexample to the claim.** `Soundness.lean:35–45` asserts:

> Page 10 displays Lemma 4.7 parts (i) and (ii) with **literally the same visible formula** …
> verified against a direct render of page 10 … landing **one** Lean fact discharges both citations.

The direct `pdftotext -layout -f 10 -l 10 source.pdf` render (reproduced verbatim above) reads:

```
   (i) If (A ∧ B) ⊃ C is provable in HCK + X, then so is ((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C).
  (ii) If (A ∧ B) ⊃ C is provable in HCK + X, then so is ((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C).
```

(i) has `(D ⊃ B)`/`(D ⊃ C)`; (ii) has `(D ∧ B)`/`(D ∧ C)`. These are different statements. The
`∧`-vs-`⊃` glyphs render cleanly in this PDF (only `□` is dropped — visible in (iii)/(iv)/`L_X`
of the same render, where Lean's `lemma4_7_iii`/`lemma4_7_iv` already correctly restore them).

**Current behaviour**: `lemma4_7_i_ii` is Lemma 4.7(i). The file has no Lemma 4.7(ii).
**Required behaviour**: land `lemma4_7_ii` and stop claiming (i)≡(ii) in the docstring.
**Isolation**: `Soundness.lean` §"Lemma 4.7", plus the module-docstring paragraph at lines 35–45.
**Why it matters**: 4.7(ii) is the *named* ingredient of the `⊃•` induction ("using an induction
on n together with Lemma 4.7.(ii) and (iv)"). Its absence is the precise, concrete reason the
task's premise "does NOT reduce to 4.4/4.5/4.8 alone" is true. It is not a deep obstruction — it
is one missing propositional lemma.

**Proved sorry-free during research** (`lean_run_code`, zero diagnostics):

```lean
/-- **Lemma 4.7(ii)** (page 10): from `⊢ (A ∧ B) ⊃ C`, derive `⊢ ((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)`. -/
theorem lemma4_7_ii (D : Proposition Atom) {A B C : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((A.and B).imp C)) :
    Derivable (@CS5ModalAxiom Atom) (((D.imp A).and (D.and B)).imp (D.and C))
```

Proof shape: one `deductionTheorem` discharge of the conjunctive hypothesis, then `andE1`/`andE2`
projections, `andI` recombination, MP against the weakened hypothesis, `andI` to rebuild `D ∧ C`.
Structurally a near-clone of the existing `lemma4_7_i_ii`, ~20 lines.

---

## Finding 2 (defect, BLOCKING): `nested_sound_impL` Is False As Stated (`ctx.Λ = []`)

**Counterexample.** Take `ctx = ⟨Γ' := [C•], Λ := [], π := P°⟩`. Lean-verified by `rfl`:

```lean
example : ((ctxCE C P).outputPruning.fillRhs (.atom A)).fm = C.imp A := rfl                       -- hA
example : ((ctxCE C P).fillLhs (.atom B)).fm = C.imp (Proposition.box (B.imp P)) := rfl           -- hB
example : ((ctxCE C P).fillLhs (.atom (A.imp B))).fm
            = C.imp (Proposition.box ((A.imp B).imp P)) := rfl                                    -- goal
```

Now instantiate `C := A` and `B := ⊥`. **Both premises are derivable — proved in Lean, sorry-free**:

```lean
theorem hA_derivable (A P : Proposition Atom) :                     -- reduces to  ⊢ A ⊃ A
    Derivable (@CS5ModalAxiom Atom) (((ctxCE A P).outputPruning.fillRhs (.atom A)).fm)
theorem hB_derivable (A P : Proposition Atom) :                     -- reduces to  ⊢ A ⊃ □(⊥ ⊃ P)
    Derivable (@CS5ModalAxiom Atom) (((ctxCE A P).fillLhs (.atom Proposition.bot)).fm)
```

(`hA` is `implyK`/`implyS` identity; `hB` is `efq` + `necessitation` + `implyK`.)

The conclusion `nested_sound_impL` would have to produce is `⊢ A ⊃ □((A ⊃ ⊥) ⊃ P)`, which is
**not** CS5-derivable: every `CS5ModalAxiom` is classically S5-valid and both rules
(MP, necessitation) preserve S5-validity, so it suffices to give a classical S5 countermodel.
Two worlds `{w, v}`, total accessibility (reflexive, symmetric, transitive); `A` true at `w`,
false at `v`; `P` false at `v`. Then `w ⊨ A`, but at `v` we have `v ⊨ A ⊃ ⊥` (since `v ⊭ A`) and
`v ⊭ P`, so `v ⊭ (A ⊃ ⊥) ⊃ P` and `w ⊭ □((A ⊃ ⊥) ⊃ P)`.

**Root cause.** `InputCtx.fillLhs` places the hole **inside an extra `.box`**
(`Γ'.fillRhs (.box (Λ.fillLhs Δ) π)`), whereas `InputCtx.outputPruning := ctx.Γ' ++ ctx.Λ` does
not account for that box when `Λ = []`. Hole depth below the `Γ'` node:

| `|Λ|` | depth in `ctx.fillLhs` | depth in `(Γ' ++ Λ).fillRhs` | consistent? |
|---|---|---|---|
| 0 | `\|Γ'\|` | `\|Γ'\| − 1` | **NO — off by one** |
| 1 | `\|Γ'\|` | `\|Γ'\|` | yes |
| `k ≥ 2` | `\|Γ'\| + k − 1` | `\|Γ'\| + k − 1` | yes |

So the first premise is one nesting level **too shallow**, i.e. strictly **weaker** than what the
rule needs (the deeper form implies the shallower one via `tBox`, not conversely) — hence an
unsound rule. This is the same off-by-one the codebase already met and papered over with `tBox`
in `Translation.lean:300` (`InputCtx.fillEmpty_imp_outputPruning_fillRhs`, restricted to
`hΛ : ctx.Λ = []`). That restriction is corroborating evidence, not a coincidence.

**Current behaviour**: `InputCtx.outputPruning ctx = ctx.Γ' ++ ctx.Λ` (`Context.lean:188`);
`NestedProof.impL` (`Rules.lean:226`) and `NestedProof.cut` (`Rules.lean:299`) both take that as
the shape of their first premise; `nested_sound_impL` is consequently refutable.

**Required behaviour**: `outputPruning` must always retain the box layer the hole sits under:

```lean
def InputCtx.outputPruning (ctx : InputCtx Atom) : OutputCtx Atom :=
  ctx.Γ' ++ (ctx.Λ.headD NestedLhs.empty :: ctx.Λ.tail)
```

`headD .empty :: tail` is the identity on non-empty `Λ` and yields `[∅]` on `Λ = []`, so this
changes **only** the `Λ = []` case — where it reproduces the source's own decomposition of
Example 2.1's `Γ₂{ }` (`Γ' = C•,[{ }]`, i.e. a `[C•, ∅]` two-layer eq. (2.2) list), which
already has the ∅ layer that the current encoding folds into `fillLhs`'s `.box` and then forgets.

**Isolation**: `Context.lean:188` (one definition). Downstream: `Rules.lean` `impL`/`cut` premise
types (no source edit needed — they are stated via `outputPruning`), `Translation.lean:300`
(becomes trivially provable: both sides converge to `Γ'.fillRhs (.box ∅ π)`), and the
`Context.lean` docstring paragraph on output pruning.

**Faithfulness note (H3 transcription discipline)**: this is a *repair toward* the source, not a
divergence from it. Under the source's Observation 2.2 / Definition 2.3, `Γ⇓{ } = Γ'{Λ{ }}` keeps
the hole exactly where `Γ{ } = Γ'{Λ{ }, Π◦}` had it; only the `Π` subtree is removed. Removing a
nesting level as well is the bug.

---

## Finding 3 (defect, BLOCKING): the Module Does Not Build — `nested_sound` Is Missing the `cut` Case

```
error: Cslib/Logics/Modal/Metalogic/Constructive/Nested/Soundness.lean:1329:2: Missing cases:
_, (NestedProof.cut (InputCtx.mk _ _ _) _ _ _)
```

`NestedProof` has nineteen constructors including `cut` (`Rules.lean:299`); `nested_sound`
(`Soundness.lean:1327`) matches on eighteen. The module docstring's "Every constructor except
`impL` is fully discharged" is inaccurate — `cut` is not merely undischarged, it is absent, and
that is a hard compile error. The tree is clean and this is committed state (`88b198bf`).

**Consequence for this task**: the invariant "`lake build` green" cannot be met by discharging
`impL` alone. The `cut` case must be handled in the same task, or the task's exit criterion is
unreachable.

**Sized path for `cut`** (the source's own one-liner: "For the cut-rule we additionally observe
that `A ⊃ A` is always provable"):

1. `cut ctx A : NestedProof (ctx.outputPruning.fillRhs A°) → NestedProof (ctx.fillLhs A•) →
   NestedProof ctx.fillEmpty`. Run the repaired `impL` argument with `B := A`; `⊢ A ⊃ A` gives
   `⊢ ⊤ ⊃ fm((A ⊃ A)•)`, so `InputCtx.fillLhs_fm_antitone` (already landed, fully general in
   `ctx`) yields `⊢ (ctx.fillLhs (A ⊃ A)•).fm ⊃ (ctx.fillLhs ∅).fm`.
2. One small bridging induction `OutputCtx.fillLhs_empty_imp_fillEmpty`:
   `⊢ (ctx.fillLhs .empty).fm ⊃ ctx.fillEmpty.fm`. The two differ only by `⊤`-conjuncts
   (`[] → equal`; `[Γ] → (L₀ ∧ ⊤) ⊃ L₀`; `Γ::Γ₂::rest → ∧`-congruence under `◇`-monotonicity),
   mirroring `OutputCtx.fillLhs_fm_mono`'s existing three-case recursion exactly.

---

## The Λ-Chain Induction: Proposed Statements, Motive, and Verified Proofs

Everything below **compiled sorry-free** under `lean_run_code` against
`import Cslib.Logics.Modal.Metalogic.Constructive.Nested.Soundness` with **zero diagnostics**.

### L1. `lemma4_7_ii` — the missing ingredient (Finding 1)

Signature as in Finding 1. Place it in `Soundness.lean` §"Lemma 4.7", immediately after
`lemma4_7_i_ii`, and rename that one's docstring to say "(i)" only.

### L2. `lambdaChain_XZ_imp_Y` — **the induction the task asks for**

```lean
/-- **The `Λ{ }`-chain induction** (page 10): `⊢ (L_X ∧ L_Z) ⊃ L_Y`. The source's "induction on
`n` … together with Lemma 4.7.(ii) and (iv)", transcribed literally. -/
theorem lambdaChain_XZ_imp_Y (A B : Proposition Atom) :
    ∀ (Λ : OutputCtx Atom),
      Derivable (@CS5ModalAxiom Atom)
        (((Λ.fillRhs (.atom A)).fm.and (Λ.fillLhs (.atom (A.imp B))).fm).imp
          (Λ.fillLhs (.atom B)).fm)
  | []              => topBase A B
  | [Λ₀]            => lemma4_7_ii Λ₀.fm (mpAnd A B)
  | Λ₀ :: Λ₁ :: rest =>
      lemma4_7_ii Λ₀.fm (lemma4_7_iv (lambdaChain_XZ_imp_Y A B (Λ₁ :: rest)))
```

**Induction motive, spelled out.** The recursion is structural on the `OutputCtx` list `Λ`,
using the file's established **three-way** split (`[]` / `[Λ₀]` / `Λ₀ :: Λ₁ :: rest`) — the same
split `OutputCtx.fillLhs` itself recurses on, and the same one `OutputCtx.fillLhs_fm_mono` and
`lemma4_8` already use. The motive is

> `P(Λ) := ⊢ ((Λ.fillRhs A°).fm ∧ (Λ.fillLhs (A⊃B)•).fm) ⊃ (Λ.fillLhs B•).fm`

with `A`, `B` **fixed outside** the recursion (they are parameters, not part of the motive), and
the recursive call taken at the structurally smaller `Λ₁ :: rest`. Reading the three cases against
the source's `Λ{ } = Λ₀, [Λ₁, [ … , [Λₙ, { }] … ]]`: `[]` is the degenerate `Λ{ } = { }` (the
source's `n = 0` with no `Λ₀` layer, where `fillRhs` supplies the `⊤` antecedent), `[Λ₀]` is
`n = 0`, and `Λ₀ :: Λ₁ :: rest` is `n ≥ 1`.

**Why each case closes.**

| Case | Goal | Discharged by |
|---|---|---|
| `[]` | `((⊤ ⊃ A) ∧ (A ⊃ B)) ⊃ B` | `topBase` (propositional; `⊤ = ⊥ ⊃ ⊥` via `efq`) |
| `[Λ₀]` | `((L₀ ⊃ A) ∧ (L₀ ∧ (A ⊃ B))) ⊃ (L₀ ∧ B)` | `lemma4_7_ii (D := L₀)` applied to `mpAnd : ⊢ (A ∧ (A ⊃ B)) ⊃ B` |
| `Λ₀::Λ₁::rest` | `((L₀ ⊃ □X′) ∧ (L₀ ∧ ◇Z′)) ⊃ (L₀ ∧ ◇Y′)` | `lemma4_7_ii (D := L₀)` applied to `lemma4_7_iv IH` |

The cons-cons step relies on one definitional identity, which holds by `rfl`:
`(buildRhsChain (Λ₁::rest) Ψ).fm = □ ((OutputCtx.fillRhs (Λ₁::rest) Ψ).fm)` — both sides reduce to
`Proposition.box (Λ₁.fm.imp (buildRhsChain rest Ψ).fm)`. That is what lets `lemma4_7_iv`'s
`□A ∧ ◇B ⊃ ◇C` shape line up with the goal with no rewriting at all.

Supporting propositional lemmas (both proved, ~10 lines each, `deductionTheorem` + `andE1/2` + MP):

```lean
theorem mpAnd  (A B : Proposition Atom) : Derivable _ ((A.and (A.imp B)).imp B)
theorem topBase (A B : Proposition Atom) : Derivable _ (((Proposition.top.imp A).and (A.imp B)).imp B)
```

### L3. `lambdaChain_step2` — the source's "But this follows from …"

```lean
theorem lambdaChain_step2 {X Y Z P : Proposition Atom}
    (h : Derivable (@CS5ModalAxiom Atom) ((X.and Z).imp Y)) :
    Derivable (@CS5ModalAxiom Atom) ((X.and (Y.imp P)).imp (Z.imp P))
```

Two nested `deductionTheorem` discharges (of the conjunction, then of `Z`). ~15 lines. Proved.

### L4. Two shape lemmas for the `Λ = []` normalisation

```lean
theorem psiX_fm (ctx : InputCtx Atom) (A : Proposition Atom) :
    (buildRhsChain (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)).fm
      = Proposition.box ((ctx.Λ.fillRhs (.atom A)).fm)

theorem primeRhs_fm (ctx : InputCtx Atom) (A : Proposition Atom) :
    ((ctx.Λ.headD .empty :: ctx.Λ.tail).fillRhs (NestedRhs.atom A)).fm
      = (ctx.Λ.fillRhs (.atom A)).fm
```

Both are `cases ctx.Λ <;> rfl`. Proved.

### L5. The assembled `nested_sound_impL`

Proved in full (with L2/L3 supplied as hypotheses so the probe stayed axiom-clean; both were
independently proved sorry-free in the same session):

```lean
theorem nested_sound_impL (ctx : InputCtx Atom) (A B : Proposition Atom)
    (hA : Derivable (@CS5ModalAxiom Atom) (ctx.outputPruning.fillRhs (.atom A)).fm)
    (hB : Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom B)).fm) :
    Derivable (@CS5ModalAxiom Atom) (ctx.fillLhs (.atom (A.imp B))).fm := by
  set ΨX := buildRhsChain (ctx.Λ.headD .empty :: ctx.Λ.tail) (NestedRhs.atom A)
  set ΨY := NestedRhs.box (ctx.Λ.fillLhs (.atom B)) ctx.π
  set ΨZ := NestedRhs.box (ctx.Λ.fillLhs (.atom (A.imp B))) ctx.π
  -- (1) Λ-chain induction, then step 2, then box-lift by Lemma 4.7(iii)
  have h4 : Derivable _ ((ΨX.fm.and ΨY.fm).imp ΨZ.fm) := by
    have h3 := lemma4_7_iii (lambdaChain_step2 (P := ctx.π.fm) (lambdaChain_XZ_imp_Y A B ctx.Λ))
    rw [psiX_fm ctx A]; exact h3
  -- (2) lift through Γ' by the already-landed Lemma 4.9 fillRhs branching lemma
  have h5 := lemma4_9_fillRhs h4 ctx.Γ'
  -- (3) transport premise 1 onto Γ'{ΨX}
  have hAX : Derivable _ (ctx.Γ'.fillRhs ΨX).fm := by
    match hΓ : ctx.Γ' with
    | []       => -- ⊤ ⊃ □L_X : `hA` gives ⊢ L_X, then `necessitation` + `implyK`
                  …
    | G :: r'  => -- `OutputCtx.fillRhs_append` (already landed) rewrites `hA` into place
                  …
  exact andMP h5 hAX hB
```

`andMP : ⊢ (U ∧ V) ⊃ W → ⊢ U → ⊢ V → ⊢ W` is a 3-line `andI` + MP combinator.

**Note the two-case split on `ctx.Γ'`, and why it is needed**: with `Γ' = G :: r'`, the landed
`OutputCtx.fillRhs_append` (which is stated only for a non-empty first list, precisely because of
the same base-case asymmetry) does the transport definitionally. With `Γ' = []`, `hA` reduces to
`⊢ L_X` outright, and the goal needs `⊢ ⊤ ⊃ □L_X` — reachable because `hA` is a **theorem**, so
`necessitation` applies. This is the one place the proof is not a uniform lift, and it is the
reason the `Γ' = []` case is *sound* even though it looks like the `Λ = []` case: a derivable
premise can be necessitated, a hypothesis inside a box cannot.

---

## Reuse Check Protocol (CSLib reuse-first)

| Step | Check | Result |
|---|---|---|
| 1 | `Cslib.Foundations.*` for the needed abstractions | Nothing applicable — this is logic-specific `fm`/context machinery, correctly local to `Nested/` |
| 2 | Existing typeclass hierarchy (`LTS`, `HasImp`, `HasBox`, …) | Not applicable; `Proposition`/`Derivable` are already the right currency |
| 3 | Notation typeclasses | No new notation needed (`◇`, `□` already in scope via `Cslib.Logics.Modal.Basic`) |
| 4 | Mathlib instantiable version | None — Hilbert-derivability over `CS5ModalAxiom` is project-local |
| 5 | `Cslib.Logics.*` / `Cslib.Foundations.Logic.*` for existing pieces | **Heavy reuse achieved** (below) |

**Reused, not re-proved** — every one of these is already landed and verified:

| Existing declaration | Location | Role in the new proof |
|---|---|---|
| `lemma4_7_iii` | `Soundness.lean:549` | box-lifts step 2 into `□`-land |
| `lemma4_7_iv` | `Soundness.lean:556` | the `□X ∧ ◇Z ⊃ ◇Y` inductive step of the Λ-chain |
| `lemma4_9_fillRhs` | `Soundness.lean:693` | lifts the branching implication through `Γ'` |
| `OutputCtx.fillRhs_append` | `Context.lean:204` | transports premise 1 for non-empty `Γ'` |
| `InputCtx.fillLhs_fm_antitone` | `Translation.lean:274` | the `cut` case (Finding 3) |
| `OutputCtx.fillLhs_fm_mono` | `Translation.lean:255` | template for the `cut` bridging induction |
| `deductionTheorem` (+ `implyK`/`implyS` feeders) | used at `Soundness.lean:507` | all four propositional lemmas |
| `cs5_soundness_derivable''` | `CS5.lean:446` | optional: turns Finding 2's countermodel into a *formal* Lean refutation |

**Nothing new needs to be defined** beyond the one-line repair to `InputCtx.outputPruning`. No new
axioms. No `sorry`. `lemma4_8` and `lemma4_5` turned out **not** to be needed for `⊃•` (the
`fillRhs`-flavoured `lemma4_9_fillRhs` is the right lift, avoiding `lemma4_8`'s `fillFull`
singleton-merge mismatch) — which independently corroborates the task's "does not reduce to
4.4/4.5/4.8" premise, though for a sharper reason than "not enough machinery".

---

## Recommended Phase Decomposition (input to `/plan`)

Zero-debt throughout; each phase ends green or is not committed.

| Phase | Scope | Files | Verification |
|---|---|---|---|
| 1 | Land `lemma4_7_ii`; correct the module docstring's (i)/(ii) "duplication" paragraph; rename `lemma4_7_i_ii` docstring to "(i)" (keep the identifier to avoid a rename cascade, or rename with a `deprecated` alias — planner's call) | `Soundness.lean` | module builds no worse than baseline; new lemma sorry-free |
| 2 | Repair `InputCtx.outputPruning`; update its docstring and the `Context.lean` "Output Pruning" section; simplify `InputCtx.fillEmpty_imp_outputPruning_fillRhs` (its `tBox` gap disappears) | `Context.lean`, `Translation.lean` | `lake build …Nested.Translation` green |
| 3 | Land `mpAnd`, `topBase`, `lambdaChain_step2`, `psiX_fm`, `primeRhs_fm`, `andMP`, and **`lambdaChain_XZ_imp_Y`** | `Soundness.lean` | all sorry-free |
| 4 | Discharge `nested_sound_impL` (remove the sorry at 1315 and its section docstring) | `Soundness.lean` | census `41 → 40`; `#print axioms nested_sound_impL` free of `sorryAx` |
| 5 | Land `OutputCtx.fillLhs_empty_imp_fillEmpty` + `nested_sound_cut`; add the `.cut` arm to `nested_sound` | `Soundness.lean` | **`lake build` RED → green** |
| 6 | Full CI: `lake build`, `lake exe checkInitImports`, `lake lint`, `lake exe lint-style`, `lake test`; re-run the sorry census | — | all green; census 40 |

**Optional hardening** (recommend including): a regression `example` in `Soundness.lean` (or
`CslibTests/`) formalising Finding 2's countermodel against `cs5_soundness_derivable''`, so the
`Λ = []` off-by-one can never silently return.

---

## Adversarial Self-Verification (H4)

Every load-bearing claim was independently re-checked before this report was written.

### Claim Verification Table

| Claim | Source/Counterexample | Verdict |
|---|---|---|
| The `⊃•` obligation needs the source's own induction on `n` over the `Λ{ }` chain | `source.pdf` p. 10 `pdftotext -layout` render, verbatim: "which can be shown provable in HCK + X using an induction on n together with Lemma 4.7.(ii) and (iv)" | **CONFIRMED** |
| It "does NOT reduce to Lemma 4.4/4.5/4.8's already-landed congruence lemmas alone" (task premise) | Verified, but the *reason* differs from the in-code note: the true blocker is that **Lemma 4.7(ii) was never landed**. Once 4.7(ii) exists, the induction is 3 lines and needs neither 4.4, 4.5 nor 4.8 — it routes through `lemma4_9_fillRhs` instead | **CONFIRMED (premise true; stated reason refined)** |
| Lemma 4.7(i) and (ii) are "literally the same visible formula" (existing docstring, `Soundness.lean:35–45`) | Direct page-10 render: (i) `((D ⊃ A) ∧ (D ⊃ B)) ⊃ (D ⊃ C)`; (ii) `((D ⊃ A) ∧ (D ∧ B)) ⊃ (D ∧ C)`. `∧`/`⊃` glyphs render cleanly in this PDF (only `□` drops — visible in (iii)/(iv), which Lean already restores correctly) | **REFUTED** — docstring is wrong |
| `L_X = L₀ ⊃ □(L₁ ⊃ □(… ⊃ □(Lₙ ⊃ A)…))` (i.e. the render's missing `□`s recovered correctly) | Not inferred from the corrupted text: Lean-verified by `rfl` against `OutputCtx.fillRhs`/`buildRhsChain`/`fm` — `((ctxOk C L P).outputPruning.fillRhs (.atom A)).fm = C.imp (□(L.imp A))` | **CONFIRMED (independently, in Lean)** |
| `nested_sound_impL` is provable as currently stated | **REFUTED by counterexample.** `ctx = ⟨[C•], [], P°⟩`, `C := A`, `B := ⊥`: both premises Lean-proved derivable (`hA_derivable`, `hB_derivable`, sorry-free); conclusion `A ⊃ □((A ⊃ ⊥) ⊃ P)` fails in a 2-world classical S5 model, and every CS5 theorem is classically S5-valid | **REFUTED** |
| The defect is confined to `ctx.Λ = []` | Depth table computed and `rfl`-checked at `\|Λ\| = 0, 1, 2`; `\|Λ\| = 1` case Lean-verified consistent (`(ctxOk …).outputPruning.fillRhs` vs `.fillLhs` both one box deep) | **CONFIRMED** |
| The proposed repair `Γ' ++ (Λ.headD ∅ :: Λ.tail)` is minimal and correct | Identity on non-empty `Λ` (so nothing else moves); on `Λ = []` it reproduces the source's own `Γ' = [C•, ∅]` decomposition of Example 2.1's `Γ₂{ }`. Independently corroborated: it makes `Translation.lean`'s `Λ = []`-restricted `tBox` bridge collapse to reflexivity — the `tBox` was papering over exactly this gap | **CONFIRMED** |
| With the repair, `⊃•` is fully dischargeable sorry-free | Assembled and **compiled** end-to-end in `lean_run_code` (`impL_repaired`), zero diagnostics, no `sorry`, no new axiom | **CONFIRMED** |
| `lambdaChain_XZ_imp_Y` is provable in three cases via 4.7(ii)+(iv) | **Compiled sorry-free**, zero diagnostics | **CONFIRMED** |
| `lake build` is currently green (task-statement invariant "lake build and lake test green") | **REFUTED.** `lake build Cslib…Nested.Soundness` fails: `1329:2: Missing cases: _, (NestedProof.cut …)`. Tree clean for `Cslib/`; committed state at `88b198bf` | **REFUTED — baseline is RED** |
| "the cut rule and NestedProof.CutFree are already landed and verified" (task premise) | Half true: `NestedProof.cut` (`Rules.lean:299`) and `NestedProof.CutFree` (`Rules.lean:361`) exist, but `nested_sound` never got a `.cut` arm — which is precisely the build error | **PARTIALLY REFUTED** |
| Cslib sorry baseline is 41 | `bash .claude/scripts/lean-sorry-census.sh Cslib` → `sorry_count: 41`; inventory lists `Soundness.lean:1315` exactly once | **CONFIRMED** |
| No existing CSLib/Mathlib abstraction already covers this | 5-step Reuse Check Protocol run (table above). Eight existing declarations reused; exactly one new definition-level change (the `outputPruning` repair) | **CONFIRMED** |
| BibKey `ArisakaDasStrassburger2015` is valid | `references.bib:939` | **CONFIRMED** |

### Claims Modified After Verification

- **Initial hypothesis**: "the Λ-chain induction is the hard part". **Revised**: the induction is
  the *easy* part (3 lines). The hard parts are the two pre-existing defects — a missing lemma and
  an unsound definition — neither of which the in-code deferral note identifies.
- **Initial reading of the deferral note** ("more machinery than this phase's scope"). **Revised**:
  the required machinery is small. What was actually missing was correctness of `outputPruning`
  and the existence of 4.7(ii). Framing this as a scope problem would have led the plan astray.
- **Considered and rejected**: routing `⊃•` through `lemma4_8` (`fillFull` flavour), as the source
  literally says ("To be able to apply Lemma 4.8"). Rejected because Lean's `OutputCtx.fillFull`
  has a singleton-case `comma Φ Γ` merge that makes `fm(Γ'.fillFull (Λ.fillRhs Ψ))` differ from
  `fm((Γ' ++ Λ).fillRhs Ψ)` by `⊤`-conjuncts, requiring a bridging *implication* rather than an
  equality. `lemma4_9_fillRhs` (already landed, uniform base case, no singleton merge) matches the
  shapes exactly. **This is a divergence from the source's stated route and is flagged as such**;
  it is a Lean-encoding artefact (`fillFull` vs `fillRhs`), not a mathematical disagreement, and
  the resulting proof still uses exactly the source's Lemma 4.7(ii)/(iv) induction.

### Uncertain Claims (with confidence)

| Claim | Confidence | Residual risk |
|---|---|---|
| Repairing `outputPruning` breaks nothing beyond `Rules.lean`/`Translation.lean`/`Context.lean` | **Medium-high** | `Completeness.lean` / `CS5Completeness.lean` were not read. `grep` shows `outputPruning` is confined to the `Nested/` module, but the first `lake build` after the Phase-2 edit is the real test. Plan should budget for fallout. |
| `nested_sound_cut` closes with the two steps sketched in Finding 3 | **Medium** | The `fillLhs ∅` vs `fillEmpty` bridge was reasoned out and hand-checked at `\|Λ\| = 0, 1, 2` but **not** compiled. It mirrors `OutputCtx.fillLhs_fm_mono`'s existing recursion, so the risk is low, but it is the one un-compiled piece in this report. |
| A formal Lean refutation of the un-repaired `impL` is constructible | **Medium** | `cs5_soundness_derivable''` exists and the countermodel is 2 worlds, but building a `CKValidFC cs5FC''` instance was not attempted. This is *optional* hardening, not on the critical path. |
| `lake test` passes after the fix | **Unknown** | Cannot be assessed while the library does not build. |

### Anti-Analysis Compliance (H2)

This dispatch did not stop at analysis. It produced **seven compiled, sorry-free Lean theorems**
during research — `lemma4_7_ii`, `mpAnd`, `topBase`, `lambdaChain_XZ_imp_Y`, `lambdaChain_step2`,
`psiX_fm`/`primeRhs_fm`, `andMP` — plus the **end-to-end assembled `impL` discharge**, plus two
compiled derivability witnesses for the counterexample. Every defect claim carries the required
four elements (counterexample, current behaviour, required behaviour, isolation). No recommendation
defers work to a `sorry` or an axiom.

---

## References

* [R. Arisaka, A. Das, L. Straßburger, *On Nested Sequents for Constructive Modal
  Logics*][ArisakaDasStrassburger2015], LMCS 11(3:7), 2015 — §2 Observation 2.2 / Definition 2.3
  (p. 5); §4 Lemmas 4.7–4.9 and Theorem 4.1 (pp. 9–10). BibKey verified at `references.bib:939`.
* Local corpus: `~/Projects/Literature/sources/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics/`
  (`source.pdf` p. 10; `chunk_0022.md`, `chunk_0023.md`).
