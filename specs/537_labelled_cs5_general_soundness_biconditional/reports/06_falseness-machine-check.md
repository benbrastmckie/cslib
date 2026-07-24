# Machine-Check: Is the Intended `nik_adequacy` False?

- **Task**: 537 — general labelled CS5 soundness biconditional
- **Type**: cslib (Lean 4) — VERIFICATION-ONLY dispatch (no library edits, no redesign)
- **Claim under test**: report `05_efq-orE-motive-defect-and-path.md` §3 — the landed
  target-oriented `nikTr` makes the intended `nik_adequacy` mathematically FALSE at the
  disconnected-`y` `efq` case.
- **Probe**: `specs/537_labelled_cs5_general_soundness_biconditional/probes/nik_adequacy_falseness.lean`
- **Verification**: `lake env lean <probe>` → exit 0, zero errors, zero warnings, zero `sorry`.
  `#print axioms` on every reductio theorem: `[propext, Classical.choice, Quot.sound]` only —
  **no `sorryAx`**.
- **`Cslib/` untouched** (`git status --short Cslib/` empty).

---

## VERDICT: **CONFIRMED** — and the falseness is broader than report 05 stated.

The intended statement is machine-refuted, not merely analytically suspect. Two independent
reductios compile:

### 1. `nik_adequacy_is_false` (the report's exact reductio)

Taking the plan-v5 statement verbatim as a hypothesis —

```
∀ G Γ hfin x A, IsDerivationForest G → NIK TS5 G Γ (x ∶ A) →
  Derivable CS5ModalAxiom (nikTr G Γ hfin x A)
```

— the probe derives `False`. Witness: `G = Graph.trivial ℕ` (a derivation forest by the landed
`forest_trivial`), `Γ = [var 0 ∶ ⊥]`, conclusion label `var 1 ∉ G.X`, `A = ⊥`. The `NIK`
derivation is two constructors: `.assumption` then cross-label `.efq`.

`nikTr_yy_explicit` pins the translation **exactly** as report 05 predicted:

```
nikTr Gt Ctx Gt_fin (var 1) A = ((⊥ ⊃ ⊥) ∧ (⊥ ⊃ ⊥)) ⊃ A
```

The graph *and* the context (which asserts `var 0 ∶ ⊥`) are discarded wholesale. The antecedent
is a CS5 theorem (`sigAt_yy_deriv`), so MP yields `Derivable CS5ModalAxiom ⊥`, contradicting the
landed `cs5_consistent_incest`.

### 2. `rooted_restricted_adequacy_is_false` (root-connectivity sub-claim — also CONFIRMED, for a
broader reason)

Report 05 said root-connectivity fails to rescue the statement *because* `y ∉ G.X` is outside
`IsRootedForest`'s scope. That is correct, but the failure survives even after plugging that
hole: the probe refutes the statement **restricted to `x ∈ G.X`**, over a single-node (hence
trivially single-rooted) forest. Witness: `Γ = [var 1 ∶ ⊥]` with `var 1 ∉ G.X`, conclusion at the
root `var 0 ∈ G.X`. Adding `IsRootedForest` to the hypothesis set changes nothing — the escape
hatch just moves from the conclusion label to the **context** label.

So the previously-planned root-connectivity invariant work is **not** the fix, confirmed twice
over.

### 3. `premise_escapes_graph` — the restriction is uninductive, not just insufficient

Adversarial check in the other direction: could adding *both* `x ∈ G.X` **and**
`labels(Γ) ⊆ G.X` (plus rootedness) rescue the landed `nikTr`? I could not construct a
counterexample to that fully-wellformed variant, and hand-analysis suggests it may in fact be
true (every node of a single-rooted tree appears somewhere in `nikTr`'s antecedent chain under
some `□`-depth, and CS5's `T` axiom collapses `□^k⊥` to `⊥`, making the antecedent contradictory).
**That variant is NOT refuted here.**

But it is not usable either, and the probe shows why mechanically: `ctx_labels_in_X` +
`premise_escapes_graph` together exhibit a context all of whose labels lie in `G.X` from which
`NIK` nevertheless derives `⊥` at a label **outside** `G.X`. In the `efq` case of an
`x ∈ G.X`-restricted induction, the premise's label is exactly such a label, so the induction
hypothesis does not apply. The restriction is uninductive at the one case the whole task is stuck
on.

---

## Implications for the plan revision

1. **Report 05's headline is machine-confirmed.** `nik_adequacy` as planned is false; the
   12-constructor induction cannot close at `efq` (and `orE` has the identical shape — `y`
   independent of `x`, `y ∉ G.X` permitted, `Deduction.lean:271`). Proceeding with the current
   `nikTr` is proceeding toward a false goal.
2. **Drop the root-connectivity work as the fix.** `IsRootedForest` is refuted as a rescue in two
   distinct ways. It may still be *needed* by the redesigned translation (to name the root
   anchoring `Θ`), but it is not the missing piece and should not be planned as such.
3. **Report 05's diagnosis of the root cause is confirmed and should be sharpened**: the defect is
   that `nikTr`'s antecedent is target-*dependent*. Every refutation above is an instance of "the
   antecedent forgets a `⊥` that lives off the target's ancestor spine." A target-independent
   `Θ(G,Γ) ⊃ place(x,A)` removes the entire family, because `Θ` cannot forget anything.
4. **The one open question the machine check does not settle**: whether the fully-wellformed
   restricted variant is true. It appears to be, but it is uninductive at `efq`, so it is not a
   viable route regardless. Do not spend a dispatch on it.
5. **Sunk-cost accounting stands as report 05 stated it**: `nikTrFuel` and its bespoke lemmas
   (`nikTrFuel_mono`, `_succ_eq`, `_no_parent`, `_fuel_invariant_step`, `sigAtFuel_mono_fuel`/`_le`)
   serve the target-oriented ancestor walk and are retired by the redesign. `sigAt`/`sigAtFuel`/
   `factsAt`/`bigAndL` and the whole `cs5_deriv_*` toolkit are preserved — the probe itself is
   built entirely out of them, which is independent evidence they are sound and reusable.
6. **Report 05's "resolve the OCR-corrupted Simpson §6.1 source before re-defining" precondition
   is reinforced**: a prose reconstruction produced a false-making definition once, and this
   dispatch is the machine confirmation of that.

---

## Probe inventory

| Theorem | What it establishes |
|---|---|
| `nik_deriv` | The two-constructor `NIK TS5` derivation at a disconnected label really exists |
| `gt_forest` | The witness graph satisfies the landed `IsDerivationForest` invariant |
| `nikTr_yy` | `nikTr` performs zero ancestor-wraps at a disconnected label |
| `nikTr_yy_explicit` | The dropped-graph formula is exactly `((⊥⊃⊥)∧(⊥⊃⊥)) ⊃ A` |
| `sigAt_yy_deriv` | That antecedent is a CS5 theorem (for every fuel value) |
| `nik_adequacy_is_false` | **The plan-v5 statement implies `False`** |
| `rooted_restricted_adequacy_is_false` | **Still `False` with the conclusion label restricted to `G.X`** |
| `ctx_labels_in_X` + `premise_escapes_graph` | The `x ∈ G.X` restriction is uninductive at `efq` |
