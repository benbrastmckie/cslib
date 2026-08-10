# Upward Closure of `minBranchBotForces` at the `⊥` Formula Shape

**Task type**: cslib (research)
**Session**: sess_1786321994_b49e26_605
**Site**: `Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean:150` (`minimalTableau_complete`), `sorry` at `:160`

## Executive Summary

Three results, all machine-checked against the real build (not sketched):

1. **The obligation is NOT independent, and it is NOT hard.** `minBranchBotForces b`'s
   upward-closure is the `χ := ⊥` instance of a fact the codebase *already proves* for
   `χ := .atom p`. The underlying invariant `IPosPersistRaw` (`Scheme.lean:6798`) is already
   quantified over **arbitrary** `χ : Proposition Atom`; only its consumer,
   `openBranch_rawEdges_upward_closed`, narrows it to atoms. Generalizing that consumer's
   conclusion from `intExtractValuation` to a bare positive-formula-membership predicate makes
   both upward-closure facts fall out of one lemma, at one shared `edges` witness. **Verified**:
   builds sorry-free in 14s.

2. **The current `hvalid` premise shape is REFUTED for `minScheme`** — a new negative result.
   Even *with* the valuation upward-closure premise `_huc` already supplied, `tableau_complete`'s
   `hvalid` is not derivable from `MValid φ`. This is the exact analogue of the already-accepted
   `CslibTests/HvalidShapeRefutation.lean` defect, one conjunct later. It means DP-4's `sorry`
   is **unclosable as currently stated** — not merely open. The statement shape must be fixed.
   **Verified**: refutation file compiles clean, zero sorries.

3. **The statement-shape fix closes DP-4 end to end.** Adding the `modelBot` upward-closure
   conjunct to `openBranch_countermodel` and the matching premise to `tableau_complete`, then
   repairing the four call sites, eliminates the DP-4 `sorry` entirely. **Verified**: full
   project build green (3325 jobs), repo sorry count in this chain goes 3 → 2. The complete
   verified diff is saved at `verified-shape-fix.patch` in this task directory.

**Net effect on the task's framing**: the "second, genuinely separate obligation" is retired as
a separate obligation. What remains at the DP-4 site after the fix is *exactly* what remains at
the DP-3 site — `openBranch_countermodel`'s single open existential in `Scheme.lean`. Two
obligations become one.

## 1. What the obligation actually is

`MValid` (`Semantics/Kripke.lean:153`) takes two upward-closure premises:

```lean
def MValid (φ : PL.Proposition Atom) : Prop :=
  ∀ (World : Type v) [Preorder World] (val : World → Atom → Prop) (bot_forces : World → Prop),
    (∀ {w w' : World} (p : Atom), w ≤ w' → val w p → val w' p) →
    (∀ {w w' : World}, w ≤ w' → bot_forces w → bot_forces w') →
    ∀ w, IForces val bot_forces w φ
```

At the DP-4 site the first is supplied as `_huc`; the second is not supplied at all. The missing
fact is upward-closure of

```lean
def minBranchBotForces (b : IBranch Atom) (w : Nat) : Prop :=
  b.any (fun sf => sf.sign == .pos && sf.formula == (HasBot.bot : Proposition Atom) && sf.label == w)
```

along `intAccessPreorder edges`.

## 2. Negative result: the current shape is refuted (new)

Contrary to the prior annotation's framing ("open, not refuted"), the DP-4 goal **as currently
stated** is refuted. `tableau_complete`'s `hvalid` quantifies over an **arbitrary** `(edges, b)`
pair with no hypothesis tying either to a tableau run. A synthetic pair breaks it while `MValid`
holds and the valuation premise is satisfied:

- `φ = ⊥ → ((⊥ → ⊥) → ⊥)` — minimally valid (needs exactly `bot_forces` upward closure)
- `edges = [(1, 0)]`, so `0 ≤ 1`
- `b = [T(⊥)@0]` — **no atoms at all**, so `intExtractValuation b` is empty and its upward
  closure holds *vacuously*

Then `minBranchBotForces b 0` holds, `minBranchBotForces b 1` fails, and
`IForces … 0 φ` is false. Machine-checked, five theorems, zero sorries, `lake env lean` clean.
The file is saved as `MvalidBotShapeRefutation.lean.verified` in this task directory (ready to
land as `CslibTests/MvalidBotShapeRefutation.lean`, mirroring `HvalidShapeRefutation.lean`).

Note the witness is *deliberately atom-free*: the failure needs no non-upward-closed valuation
at all, which isolates it cleanly from the conjunct-1 defect.

**Relation to the retraction in the current docstring.** No contradiction. The retraction is
about the *real* `phiRef1` tableau branch, where `[(1,0)]` happens to satisfy both obligations.
That remains true. The refutation here is about `hvalid`'s **arbitrary** `b`, which the real
branch does not constrain. Both facts stand; they are about different quantifiers.

## 3. Positive result: the ⊥ instance is free

`IPosPersistRaw` (`Scheme.lean:6798`) is already `∀ χ`:

```lean
private def IPosPersistRaw (edges : IEdges) (b : IBranch Atom) : Prop :=
  ∀ (χ : Proposition Atom) (w w' : Nat), isAccessible edges w w' = true →
    (⟨.pos, χ, w⟩ : ISF Atom) ∈ b → b.any (fun sf => sf.label == w') = true →
    (⟨.pos, χ, w'⟩ : ISF Atom) ∈ b
```

`openBranch_rawEdges_upward_closed` (`Scheme.lean:8054`) consumes it only at `χ := .atom p`.
Generalizing its conclusion:

```lean
    ∃ edges : IEdges,
      ∀ (χ : Proposition Atom) {w w' : Nat}, @LE.le Nat (intAccessPreorder edges).toLE w w' →
        b.any (fun sf => sf.sign == .pos && sf.formula == χ && sf.label == w) = true →
        b.any (fun sf => sf.sign == .pos && sf.formula == χ && sf.label == w') = true
```

The proof body needs only three token substitutions (`.atom p` → `χ`, drop the
`intExtractValuation` unfolds, bind `χ` in the `intro`). Both facts then derive at **one shared
`edges`**:

```lean
  · intro w w' p hle hval; exact hgen (.atom p) hle hval          -- valuation
  · intro w w' hle hbot;   exact hgen (HasBot.bot) hle hbot       -- ⊥
```

Verified sorry-free. `minBranchBotForces` and `intExtractValuation` are literally the same
`List.any` shape at different formula constructors, so no coercion friction arises.

### Frame generality

Upward closure is *anti-monotone* in the edge set, so the result is not `rawEdges`-specific. Two
new lemmas (proved, ~35 lines, modelled verbatim on the existing
`isAccessible_go_append_mono` / `isAccessible_go_fuel_mono` pair) establish it:

```lean
private lemma isAccessible_subset_mono {edges edges' : IEdges}
    (hsub : ∀ e ∈ edges, e ∈ edges') (hlen : edges.length ≤ edges'.length) {w w' : Nat}
    (h : isAccessible edges w w' = true) : isAccessible edges' w w' = true

lemma intAccessPreorder_mono_subset  -- lifts through Relation.ReflTransGen.mono
```

Consequence: both upward-closure facts transfer to **any sub-frame of `rawEdges`** — which is
the admissible edge space `openBranch_countermodel`'s docstring already characterises. So
whatever witness that lemma eventually commits to, if it is a sub-frame of `rawEdges`, the ⊥
obligation comes along for free.

## 4. The end-to-end fix (verified, patch attached)

Four edits plus two call-site repairs, all verified together:

| File | Change |
|---|---|
| `Scheme.lean` | `openBranch_countermodel`: add third conjunct `∀ {w w'}, w ≤ w' → S.modelBot b w → S.modelBot b w'` (goes behind the *existing* `sorry`; no new sorry) |
| `Scheme.lean` | `tableau_complete`: `hvalid` gains the matching premise; destructure 4-tuple |
| `Scheme.lean` | generalize `openBranch_rawEdges_upward_closed` to `∀ χ`; add the two monotonicity lemmas |
| `Intuitionistic/Completeness.lean` | mirror conjunct on `intuitionisticOpenBranch_countermodel`; `intro … _hbuc`. For `intScheme`, `modelBot = fun _ => False`, so the conjunct is trivial — **zero cost on the intuitionistic side** |
| `Minimal/Completeness.lean` | mirror conjunct; **replace the DP-4 `sorry`** with `exact @h Nat (intAccessPreorder edges) (intExtractValuation _b) (minBranchBotForces _b) _huc _hbuc 0` |

### Discovered blocker: a universe pin is required

The existing DP-3 docstring claims `exact h Nat (intExtractValuation _b) _huc 0` "would
type-check". **That claim is false as written** — verified:

```
Application type mismatch: ℕ has type Type of sort `Type 1`
but is expected to have type Type u_2
```

`MValid.{u,v}` quantifies `World : Type v`; the countermodel frame is `Nat : Type 0`. The
theorem's own bound universe parameter cannot be instantiated. The statement must pin
`(h : MValid.{_, 0} φ)`. This is a *strengthening* (weaker hypothesis), not a weakening.

The pin ripples to exactly two downstream declarations in
`Minimal/DecisionProcedure.lean` (`minimalTableau_decides`, `instDecidableMValid`), and then to
`instDecidableDerivableMinPropAxiom`, which needs `Decidable (MValid.{u,u} φ)`. Resolved with a
universe-invariance bridge, both directions proved:

- `MValid.{_,0} → MValid.{_,v}`: **free** — complete at `0`, then apply the
  universe-polymorphic `minimalTableau_sound` at `v`.
- `MValid.{_,v} → MValid.{_,0}`: a ~20-line `ULift` transport (`Preorder.lift ULift.down`, plus
  an induction on `φ` showing forcing commutes with `ULift.down`). Proved and building.

The same universe pin will be needed on the DP-3 side whenever that site is closed. Worth
recording independently of this task.

## 5. Verification record

| Check | Result |
|---|---|
| `MvalidBotShapeRefutation` (5 theorems) | `lake env lean` clean, zero errors, zero sorries |
| `lake build …Intuitionistic.Scheme` with χ-generalization + both derivations | green, 14s, only the pre-existing `openBranch_countermodel` sorry |
| `lake build …Minimal.Completeness` with shape fix | green, **sorry-free** |
| `lake build …Minimal.DecisionProcedure` with universe bridge | green (961 jobs) |
| `lake build` (full project) | **green, 3325 jobs**; remaining sorries: `Scheme.lean:8066`, `Int/Completeness.lean:162` |
| Working tree | reverted to pristine after probing; patch saved separately |

Sorry census for this chain: **3 → 2** (DP-4 eliminated). No new sorries. No new axioms.

## 6. Recommendation

Land the fix as scoped above, with one judgement call for the planner.

**On whether to actually close DP-4's `sorry`.** The intuitionistic sibling deliberately keeps
DP-3's `sorry` even though (modulo the universe pin) it could be closed, on the stated ground
that closing it would "launder" the still-open `openBranch_countermodel` conjunct through the
file. The identical argument applies to DP-4. Two defensible options:

- **(A) Close it** (what the verified patch does). Defensible because the *shape* defect is now
  refuted, and the honest residual — `openBranch_countermodel`'s existential — is already marked
  `sorry` one level down. Reduces double-counting of a single obligation.
- **(B) Keep the `sorry`, land everything else.** Preserves exact parity with the DP-3 site's
  discipline. Still a large win: the ⊥ obligation is discharged, the shape defect is refuted and
  documented, and the annotation shrinks from "two open obligations" to one.

**Recommendation: (A)**, with the DP-4 annotation rewritten to say plainly that the site now
rests on `openBranch_countermodel` alone, and a matching note added to the DP-3 site recording
the universe-pin finding. Rationale: the repo's honesty discipline is about not *hiding*
obligations, and after this change nothing is hidden — the single real obligation is visible at
exactly one place instead of being redundantly re-marked at three. If the maintainer prefers
strict parity with DP-3, (B) costs only the last two lines of the patch.

**Zero-debt compliance**: no sorry deferral proposed, no axioms introduced, no vacuous
definitions. Every claim above is backed by a green build.

## Suggested phasing

1. χ-generalize `openBranch_rawEdges_upward_closed`; add the two monotonicity lemmas. (Isolated,
   sorry-free, independently valuable.)
2. Land `CslibTests/MvalidBotShapeRefutation.lean`.
3. Statement-shape fix in `Scheme.lean` + the two `Completeness.lean` call sites.
4. Universe pin + `ULift` bridge in `DecisionProcedure.lean`.
5. Rewrite the DP-4 / DP-3 annotations to match the new disposition.

## References

* [M. Fitting, *Proof Methods for Modal and Intuitionistic Logics*][Fitting1983], Chapter 4
