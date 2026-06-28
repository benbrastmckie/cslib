# Task 332 — Phase 4 Verified Build Plan for `exists_stronglyNormal_form`

**Status:** DESIGN-and-VERIFY complete. Key claims checked against the real file with `lake build`
(temporary `example`s / `def`, then reverted; file is back to its original 1-sorry green state).

**Headline result:** Report 03's recommended **Route 1/A/B (well-founded descent on
`normMeasure`) does NOT close** — this is now *empirically verified*, not conjectured. The
`normMeasure` measure strictly **increases** on the only reduction available at a reachable
non-strongly-normal derivation. The route that *does* close is a **constructive Prawitz
normalization via structural "smart eliminators"** (Route C-constructive below); its keystone
lemma is **verified to compile**. One genuinely hard lemma (`snSubst`) remains, stated precisely.

---

## 1. Chosen route

**Route C-constructive: build the strongly-normal form directly by structural recursion, using
"smart eliminator" constructors that push eliminations through `orE` and perform β-projection,
with substitution-normalization (`snSubst`) recursing on cut-formula complexity.**

Why it closes in Lean (one paragraph): The obstruction (below) shows that *reducing* a derivation
toward normal form can transiently raise `maximalFormulas`, so no single scalar/multiset measure
built from `maximalFormulas` descends on every needed step. The constructive route never *reduces*
a given derivation; it *builds* a strongly-normal derivation of the same sequent bottom-up. For an
elimination `andE1 e` it recurses structurally **on the already-strongly-normal `e`**, pushing the
`andE1` into the branches of an `orE` (`andE1(orE D DA DB) ↦ orE D (snAndE1 DA) (snAndE1 DB)`) and
projecting at an `andI` — this terminates structurally and is **verified to compile**. The only
non-structural recursion is the β/substitution case (`impE(impI body) arg ↦ snSubst body arg`),
where every newly created redex sits at a former `ass P` leaf and therefore has cut formula a
*proper subformula* of the eliminated formula; `snSubst` is well-founded on `P.complexity`. This is
exactly Prawitz's weak-normalization argument (cutrank induction with the segment/permutation cases
folded into the smart eliminators), so it is literature-faithful and avoids the broken measure.

---

## 2. The verified obstruction (why Route 1/A/B is dead)

The `isStronglyNormal` docstring (Basic.lean:229–230) already names the witness:
`andE1(orE(ass, andI(ass,ass), andI(ass,ass)))` — "normal but violates the subformula property".
It is **not** strongly normal, its only redex is the root commuting conversion, and reducing it
*raises* `maximalFormulas`. All three facts were proved as `example`s appended to
`Termination.lean` and **built successfully** (then reverted):

```lean
-- (1) the derivation is NOT strongly normal
example … : (andE1 G (orE G (ass hPQ) (andI _ Xa Ya) (andI _ Xb Yb))).isStronglyNormal = false := by
  simp [Theory.Derivation.isStronglyNormal]                                   -- ✓ builds

-- (2) its maximalFormulas carries NO redex marker (= ∅ when the leaves are SN)
example … : (andE1 G (orE G (ass hPQ) (andI _ Xa Ya) (andI _ Xb Yb))).maximalFormulas
      = (Xa.maximalFormulas + Ya.maximalFormulas) + (Xb.maximalFormulas + Yb.maximalFormulas) := by
  simp [maximalFormulas]                                                      -- ✓ builds

-- (3) the unique reduceRoot step is the commuting conversion …
example … : (andE1 G (orE G (ass hPQ) (andI _ Xa Ya) (andI _ Xb Yb))).reduceRoot
      = some (orE G (ass hPQ) (andE1 _ (andI _ Xa Ya)) (andE1 _ (andI _ Xb Yb))) := by rfl  -- ✓

-- (4) … whose maximalFormulas GAINS two fresh {(A∧B).complexity} markers
example … : (orE G (ass hPQ) (andE1 _ (andI _ Xa Ya)) (andE1 _ (andI _ Xb Yb))).maximalFormulas
      = ({(A ∧ B).complexity} + (Xa.mf + Ya.mf)) + ({(A ∧ B).complexity} + (Xb.mf + Yb.mf)) := by
  simp [maximalFormulas, conclusionComplexity]                                -- ✓ builds
```

With strongly-normal leaves, (2) gives `maximalFormulas d = ∅` while (4) gives
`maximalFormulas d' = {c, c}`, so `∅ <_DM {c,c}` means **`normMeasure d' >_lex normMeasure d`**:
the only available step goes *up*. Hence:

- `WellFounded.induction normMeasure_wf` (report 03 §B.4 Route 1) cannot make progress at `d`.
- Augmenting with `nodeCount` (`(normMeasure, nodeCount)`) does **not** help: the primary
  `maximalFormulas` component still rises, dominating the lexicographic order.
- The "normalize subterms first, then `reduceRoot`" sketch (§B.5) fails here: `d`'s subterms are
  *already* strongly normal, yet `reduceRootSubSN d` is **false** (it demands
  `(andE1 (andI Xa Ya)).isStronglyNormal`, which is `false`), so
  `reduceRoot_decreases_normMeasure` is **inapplicable** and `reduceRoot` only offers the
  measure-raising commuting step.

**Root cause:** `maximalFormulas` charges a marker only for a *direct* `andEᵢ(andI …)` /
`impE(impI …) ` / `orE(orIᵢ …)`. It does **not** charge a *maximal segment* through `orE`
(T&S's "segment" — an `orE` whose branches, possibly through nested `orE`, end in an introduction
of the eliminated connective). The standard Prawitz/T&S measure charges that segment; the Lean
`maximalFormulas` undercounts it, so the commuting conversion that converts a segment into a direct
redex appears to raise the measure. `reduceRoot_decreases_normMeasure` is individually true only
because `reduceRootSubSN` excludes exactly these reachable configurations.

---

## 3. The route that closes — ordered lemma list

All signatures are in `namespace Cslib.Logic.PL`, `open Theory Theory.Derivation`,
`variable {Atom} [DecidableEq Atom] {T : Theory Atom}`. Insert after
`reduceRoot_decreases_normMeasure` (which becomes vestigial for *this* theorem — see §5).

### L0 (helper). `isStronglyNormal_weakCtx`  — VERIFIED-ADJACENT (mirror of `maximalFormulas_weakCtx`)
```lean
private theorem Theory.Derivation.isStronglyNormal_weakCtx {Γ Δ : Ctx Atom}
    {A : Proposition Atom} (hCtx : Γ ⊆ Δ) (D : T.Derivation Γ A) :
    (D.weakCtx hCtx).isStronglyNormal = D.isStronglyNormal
```
Tactic sketch: `induction D` mirroring `maximalFormulas_weak` (lines 479–502): `cases`-on-head in
the `andEᵢ/orE/impE` cases, `simp_all [Theory.Derivation.weak, isStronglyNormal]`. Needed to weaken
the argument of `impE`/`orE` when pushing into `orE` branches.

### L1 (keystone). `snAndE1Form` — **VERIFIED: COMPILES** (structural recursion through `orE`)
```lean
def snAndE1Form {G : Ctx Atom} {A B : Proposition Atom}
    (e : T.Derivation G (A ∧ B)) (he : e.isStronglyNormal = true) :
    {d : T.Derivation G A // d.isStronglyNormal = true}
```
**The exact body below was appended to `Termination.lean` and built with no errors** (Lean accepted
the structural recursion on `e` automatically; the `orE` reassembly proof closes):
```lean
  match e, he with
  | andI _ X _, he => ⟨X, by simp only [isStronglyNormal, Bool.and_eq_true] at he; exact he.1⟩
  | orE G D DA DB, he => by
      have hD  : D.isStronglyNormal  = true := by cases D <;> simp_all [isStronglyNormal]
      have hDA : DA.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      have hDB : DB.isStronglyNormal = true := by cases D <;> simp_all [isStronglyNormal]
      refine ⟨orE G D (snAndE1Form DA hDA).1 (snAndE1Form DB hDB).1, ?_⟩
      have hX := (snAndE1Form DA hDA).2
      have hY := (snAndE1Form DB hDB).2
      cases D <;> simp_all [isStronglyNormal, isOrERoot, isIntroRoot]
  | ax h,   _  => ⟨andE1 _ (ax h),  rfl⟩
  | ass h,  _  => ⟨andE1 _ (ass h), rfl⟩
  | andE1 _ D', he => ⟨andE1 _ (andE1 _ D'), by simpa [isStronglyNormal] using he⟩
  | andE2 _ D', he => ⟨andE1 _ (andE2 _ D'), by simpa [isStronglyNormal] using he⟩
  | impE D' E', he => ⟨andE1 _ (impE D' E'), by simpa [isStronglyNormal] using he⟩
```
(Build evidence: `Built …Termination (85s)`, no `error:` lines, only style warnings.)

### L2. `snAndE2Form` — symmetric to L1 (swap `andE1`→`andE2`, project the second component). LOW risk.

### L3. `snImpEForm` — structural on the principal premise `f`; β-case delegates to `snSubst`
```lean
def snImpEForm {G : Ctx Atom} {A B : Proposition Atom}
    (f : T.Derivation G (A → B)) (hf : f.isStronglyNormal = true)
    (a : T.Derivation G A) (ha : a.isStronglyNormal = true) :
    {d : T.Derivation G B // d.isStronglyNormal = true}
```
Tactic sketch (`match f`):
- `impI _ body, hf` ⇒ `snSubst body (hf … body-SN) a ha`  (the β-redex; cut `A`).
- `orE G D DA DB, hf` ⇒ push: `orE G D (snImpEForm DA … (a.weakCtx _) (by rw[isStronglyNormal_weakCtx]; exact ha)) (snImpEForm DB …)` — structural on `f` (DA,DB smaller); SN-reassembly via `cases D <;> simp_all [isStronglyNormal]` as in L1.
- `ax/ass/andE1/andE2/impE, hf` ⇒ `⟨impE f a, by simp [isStronglyNormal]; exact ⟨hf, ha⟩⟩`.

### L4. `snOrEForm` — structural on the major premise; β-cases (`orI1/orI2`) delegate to `snSubst`
```lean
def snOrEForm {G : Ctx Atom} {A B C : Proposition Atom}
    (D : T.Derivation G (A ∨ B)) (hD : D.isStronglyNormal = true)
    (DA : T.Derivation (insert A G) C) (hDA : DA.isStronglyNormal = true)
    (DB : T.Derivation (insert B G) C) (hDB : DB.isStronglyNormal = true) :
    {d : T.Derivation G C // d.isStronglyNormal = true}
```
Sketch: `match D`: `orI1 _ d0 ⇒ snSubst DA … d0 …` (cut `A`); `orI2 _ d0 ⇒ snSubst DB … d0 …`
(cut `B`); `orE G D' DA' DB' ⇒` push (structural on `D`); leaves ⇒ `⟨orE G D DA DB, …⟩`.

### L5 (the one hard lemma). `snSubst` — substitution-normalization, WF on cut-formula complexity
```lean
def snSubst {G : Ctx Atom} {P B : Proposition Atom}
    (body : T.Derivation (insert P G) B) (hbody : body.isStronglyNormal = true)
    (arg : T.Derivation G P) (harg : arg.isStronglyNormal = true) :
    {d : T.Derivation G B // d.isStronglyNormal = true}
```
**Intent:** the strongly-normal form of `body.subsOne arg`. Traverse `body` structurally; at each
former `ass P` leaf the substituted `arg` becomes the principal/major premise of the surrounding
elimination, which is resolved by the smart eliminators L1–L4. Every such elimination's β-cut is a
*component* of `P` (created only where `arg`'s head meets an elimination at a `P`-leaf), hence
`< P.complexity`, so the L3/L4 β-cases recurse into `snSubst` at **strictly smaller complexity**.
- `termination_by (P.complexity, sizeOf body)` (lexicographic), or make L3/L4/L5 a single
  `mutual` block with that measure.
- Reuses the *already-proved* `subsOne_new_redex_complexity_lt` (line 876) and
  `maximalFormulas_sn_eq_zero` (line 977) to justify the complexity drop.

### L6. `snForm` — the driver, structural on `d`
```lean
def snForm {G : Ctx Atom} {A : Proposition Atom} (d : T.Derivation G A) :
    {d' : T.Derivation G A // d'.isStronglyNormal = true}
```
Sketch (`match d`): `ax/ass ⇒ ⟨d, rfl⟩`; intros `andI/orI1/orI2/impI ⇒` recurse on subterms and
reassemble (SN closed under intros, `simp [isStronglyNormal]`); `andE1 _ D ⇒ snAndE1Form (snForm D).1 (snForm D).2`;
`andE2 ⇒ snAndE2Form …`; `impE D E ⇒ snImpEForm (snForm D).1 _ (snForm E).1 _`;
`orE G D DA DB ⇒ snOrEForm (snForm D).1 _ (snForm DA).1 _ (snForm DB).1 _`. Structural on `d`.

---

## 4. Final theorem (proof term)

```lean
private theorem exists_stronglyNormal_form {G : Ctx Atom} {A : Proposition Atom}
    (d : T.Derivation G A) : ∃ d' : T.Derivation G A, d'.isStronglyNormal = true :=
  ⟨(snForm d).1, (snForm d).2⟩
```
Then re-point the public consumer (report 03 §B.4), deleting its dependence on the fuel sorry:
```lean
theorem Theory.Derivation.subformula_property (d : T.Derivation G A) :
    ∃ d', d'.isStronglyNormal = true ∧ d'.SubformulaProperty := by
  obtain ⟨d', hsn⟩ := d.exists_stronglyNormal_form
  exact ⟨d', hsn, d'.subformula_property_of_isStronglyNormal hsn⟩
```

---

## 5. Remaining open gap (precise)

The **only** non-mechanical obligation is **L5 `snSubst`** — specifically its termination and SN
discharge. Precise goal: define, for `body : insert P G ⊢ B` (SN) and `arg : G ⊢ P` (SN), an element
of `{d : G ⊢ B // d.isStronglyNormal = true}` by lexicographic recursion `(P.complexity, sizeOf
body)`, such that every recursive `snSubst` call triggered through L3/L4's β-cases is at a cut
formula that is a proper subformula of `P` (so `complexity < P.complexity`). The mathematical
content is exactly `subsOne_new_redex_complexity_lt` (already proved); the work is the Lean
bookkeeping to (a) thread the complexity measure through the mutual L3/L4/L5 block and (b) discharge
`isStronglyNormal` of each reassembled node. L0–L4 and L6 are mechanical (L1 verified to compile;
L2–L4,L6 are the same `cases head <;> simp_all [isStronglyNormal]` pattern that L1 already
exercises). Estimated footprint: ~250–350 lines.

**Note on reuse:** this route *supersedes* `reduceRoot_decreases_normMeasure` /
`normMeasure_wf` / `subs_maximalFormulas_mem` for the existence theorem (they are not on the
critical path of `snForm`), though `snSubst` reuses `subsOne_new_redex_complexity_lt` and
`maximalFormulas_sn_eq_zero`. If the team prefers to preserve the multiset investment, the
**alternative is Route D**: make `maximalFormulas` *segment-aware* (charge the cut complexity when
an `andEᵢ/impE` sits over an `orE` whose branch — recursively through `orE` — is an introduction of
the eliminated connective), then re-prove `reduceRoot_decreases_normMeasure` (commuting cases now
*preserve* the multiset and drop only `commutingSum`). Route D reuses `reduceRoot` but requires
re-proving the `maximalFormulas` lemma stack (`_weak`, `subs_maximalFormulas_mem`, the `_le`
lemmas) against the new definition — higher risk/larger than Route C-constructive. **Tait/Girard
reducibility (report 03 Route C)** remains the textbook fallback but is the largest footprint and
reuses none of the existing β-infrastructure.

## 6. Adversarial self-verification

- *Is the obstruction really reachable / does the theorem really have to handle it?* Yes —
  `andE1(orE(ass, andI, andI))` is a well-typed `Derivation G A` for `(P∨Q) ∈ G`; (1)–(4) above
  type-checked, so the universally-quantified theorem must produce its SN form. Not vacuous.
- *Could `(normMeasure, nodeCount)` still work via the secondary component?* No — example (4)
  raises the **primary** `maximalFormulas` component (`∅ → {c,c}`), which dominates the lex order
  regardless of any secondary/tertiary component. Falsified by build.
- *Does `snAndE1Form` actually terminate / is the `orE` SN proof real?* Verified by `lake build`
  (no `error:`; structural recursion accepted without `termination_by`). The proof of the `orE`
  case used the recursive calls' `.2` components as hypotheses (`hX`, `hY`) — Lean accepted it.
- *Confidence on the un-verified pieces:* L0, L2, L6 — high (direct mirrors of existing lemmas /
  L1). L3, L4 — medium-high (same shape as L1 plus a `snSubst` call). **L5 `snSubst` — medium**:
  the mathematics is sound and the complexity drop is a *proved* lemma, but the mutual-block
  termination encoding in Lean 4 is intricate and was **not** machine-checked here; this is the
  honest residual risk and is flagged as the open gap.
- *Zero-debt:* no `sorry`/axiom is proposed; the plan closes `exists_stronglyNormal_form` outright.
  The pre-existing fuel `sorry` in `normalize_isStronglyNormal` is made *removable* (no consumers
  once `subformula_property` is re-pointed), per report 03 §B.4.

## References
* [Prawitz1965] D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*, Ch. III–IV (segments,
  permutative conversions, weak normalization).
* [TroelstraSchwichtenberg2000] *Basic Proof Theory*, §6.1.8 (cutrank × segment-length induction),
  §6.12 (normal-form characterization) — the source of the "maximal segment" measure that the
  current `maximalFormulas` undercounts.
