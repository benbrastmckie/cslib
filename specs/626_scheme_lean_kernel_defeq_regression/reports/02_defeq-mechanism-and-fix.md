# Scheme.lean Non-Termination: Exact Mechanism and Fix

**Status**: mechanism proven experimentally; fix implemented and gate-verified in an isolated worktree
**Investigated**: 2026-08-11
**Subject**: `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean` (decl 241,
`intExpandBranches_openBranch_sat`, line 8327) against branch `task-619-phase8-wip` (commit `1e88ad3e`)
**Supersedes**: `01_scheme-defeq-regression-findings.md` section 4's "kernel-level defeq" mechanism
claim (refuted below with counter-evidence, per the prior report's own request to confirm or refute
before building a fix); the prior report's localization (section 3) and control experiment
(section 2) are confirmed and reused.

---

## 1. Executive summary

The non-termination is **not kernel defeq** and **not instance-projection unfolding**. It is
**exponential elaborator backtracking over parser `choice` nodes**, caused by a *token-and-precedence
collision* that phase 8 imports into every `Cslib.Logic.*` namespace:

- `Cslib/Foundations/Logic/Operators.lean:45` declares `scoped infixr:25 " → " => HasImp.imp` —
  the **same token, same precedence, same associativity** as Lean's core function arrow
  (`→`, infixr:25).
- `Cslib/Foundations/Logic/Operators.lean:38` declares `scoped infixr:30 " ∨ " => HasOr.or` —
  identical collision with core `Or` notation (`∨`, infixr:30).

Phase 8's `Connectives.lean` gains `public import Cslib.Foundations.Logic.Operators`
(diff hunk, `Cslib/Foundations/Logic/Connectives.lean:10` on the branch), which puts those scoped
notations in scope inside every descendant namespace of `Cslib.Logic` — including
`Cslib.Logic.PL`, where all of `Scheme.lean` lives. From that point on, **every source-level `→`
between `Prop`-level terms parses as a two-way `choice` node**, and a right-nested chain of *n*
arrows costs **Θ(2^n)** elaboration time. `Scheme.lean:8410` (`suffices key : ...`) is a single
term containing **29 `→` tokens** — 2^29 ≈ 5.4×10^8 backtracking alternatives — which is the
"non-termination" (it is astronomically slow, not divergent).

The fix is two characters: bump the two colliding precedences by one
(`infixr:26 " → "`, `infixr:31 " ∨ "`), exactly the pattern `HasAnd.and` **already uses**
(`infixr:36` vs core `∧` at 35 — measured collision-free). With this change the full
`Scheme.lean` builds in **29s** and probe chains drop from 46s to 1.6s. Formula-level notation
semantics are unchanged (verified by `rfl` and grouping tests).

---

## 2. Why the prior report's observations misled (and what they actually meant)

The prior report inferred "kernel-level defeq" from: (a) `maxHeartbeats 40000` produced no
deterministic timeout after 400s; (b) flat 455MB RSS; (c) one pegged core. All three are
reproduced and explained by the choice-backtracking mechanism:

1. **Heartbeat immunity**: ambiguous-notation alternatives are elaborated by
   `Lean.Elab.Term.elabAppFn` folding over the `choice` node's children
   (toolchain source `src/lean/Lean/Elab/App.lean:2062-2066`, v4.33.0-rc1), each alternative run
   under the `observing` combinator (`App.lean:1939`), which **catches exceptions — including the
   deterministic-timeout error — and records them as per-alternative failures** for
   `mergeFailures` (`App.lean:1903-1914` comment block). So the heartbeat budget caps work *per
   alternative* but does **not** bound the *number of alternatives walked*. The timeout error only
   surfaces after the whole 2^n walk finishes.
2. **Measured proof of (1)**: with `set_option maxHeartbeats 1000` (a budget that, if binding,
   fails in <1s), an n-arrow probe chain still runs the full exponential walk before erroring:
   n=16 → 1.9s, n=20 → 4.3s, n=24 → **46.5s** (×16 per +4 arrows = 2^n; see section 4 table).
   For n=29 that extrapolates to ≈25-50 min of walk before any error can surface — the prior
   report's 400s observation window was simply shorter than the walk.
3. **Flat RSS**: failed alternatives are discarded as they are walked; the tree is never
   materialized. CPU-bound single-threaded backtracking, no net allocation growth.

Additional correction to the prior report's section 3 ("everything before decl 241 elaborates in
well under half a minute"): with migrated dependencies, the prefix through decl 240 does
*terminate* in ~29s but **does not succeed** — `intExpandBranches_closed_unsat`
(`Scheme.lean:6264`, whose own `suffices` chain has ~16 Prop-level arrows) deterministically fails
with `(deterministic) timeout at 'whnf', maximum number of heartbeats (200000)` at line 6255,
plus two knock-on `(kernel) unknown constant` errors at 6926/6993. Reproduced twice (standalone
`lake env lean` probe and a real truncated `lake build` of the module). This error is invisible in
a full-file build because lake only flushes a module's log when the module finishes — and decl 241
never finishes. So "no diagnostic is ever emitted" (prior report section 1) was an artifact of log
buffering, not of the failure mode.

---

## 3. The mechanism, named precisely

### 3.1 What changed between main and 1e88ad3e

For `Scheme.lean`'s elaboration environment the *only* operative changes are
(full diff `git diff main 1e88ad3e` inspected):

1. `Cslib/Foundations/Logic/Connectives.lean`: adds `public import Cslib.Foundations.Logic.Operators`
   and deletes its own (duplicate) `HasImp`/`HasBox`/`HasDiamond`/`HasAnd`/`HasOr` class
   declarations. This is what puts Operators' scoped notation in scope for all of `Cslib.Logic.*`.
2. `Cslib/Logics/Propositional/Defs.lean`: deletes the three constructor-bound scoped notations
   (`infix:36 " ∧ " => Proposition.and`, `infix:35 " ∨ " => Proposition.or`,
   `infix:30 " → " => Proposition.imp`) and rewrites one `grind` proof. The
   `HasAnd`/`HasOr`/`PropositionalConnectives` instances and bridge lemmas **already exist on
   main** — they are not part of the change.

### 3.2 Why deleting those notations detonates `Scheme.lean`

Pre-migration, inside `Cslib.Logic.PL`, a `Prop`-level `A → B → C` had exactly **one** parse: the
old `Proposition.imp` notation was non-associative `infix:30`, so for a *chain* its right operand
(needing prec ≥ 31) could not itself be an arrow — only the all-core-arrow parse survives, no
`choice` node, linear cost. Control measurement: 24-arrow chain, pre-migration deps → **2.3s
(flat, = baseline import cost)**.

Post-migration, `HasImp.imp` notation is `infixr:25` — *identical* in token, precedence, and
associativity to the core arrow. Both parsers accept at every position of a chain, and mixed
nestings are all precedence-legal, so the parser emits nested `choice` nodes and the elaborator
backtracks over ~2^n interpretation assignments. Each failing `HasImp` attempt additionally pays
a failed `HasImp Prop` instance search plus a full coercion-chain enumeration —
`set_option diagnostics true` on `intExpandBranches_closed_unsat` shows the signature:
`PropositionalConnectives.toHasImp ↦ 3180`, `instPropositionalConnectivesProposition ↦ 3178`, and
a uniform `↦ 2045` across ~40 `Coe*`/algebra instances, with reducible `IBranch` unfolded 37,884
times — all for a lemma whose migrated-notation content is *zero* (every `→` in it is a function
arrow).

### 3.3 The specific term that "does not terminate"

`Scheme.lean:8410`: the `suffices key : ∀ (pending ...) ..., IAllConsistent ... → ... →
intExpandBranches.go ... = .openBranch b → ∃ ...` statement of
`intExpandBranches_openBranch_sat` is one elaboration unit containing **29 `→` tokens**
(26-hypothesis implication chain + arrows in the ∃-tail). At the measured per-alternative walk
rate (46.5s for 2^24), 2^29 ≈ **25-50 minutes** — matching the observed >34min non-completion.
The same file has a second casualty, `intExpandBranches_closed_unsat` (`Scheme.lean:6264`,
~16-arrow `suffices` chain), which is 2^13 times cheaper and therefore *does* hit the 200000
heartbeat cap and error out (section 2). The three other `go.induct` lemmas (lines 6103, 6327,
7073) have 2-4-arrow chains and pass unnoticed — every statement in the hierarchy silently pays
a 2^(arrow-chain-length) tax.

Why only `Scheme.lean` died: hypothesis telescopes written as parenthesized binders
(`(h1 : A) (h2 : B) : C`) contain no `→` tokens and are immune; `Scheme.lean` is the one file
that states worklist invariants as long explicit implication chains inside `suffices`/`have`
terms.

### 3.4 The `∧`/`∨`/`→` collision table (measured)

| Operator | Operators.lean scoped notation | Core notation | Collision | 24-chain, hb=1000, branch deps |
|---|---|---|---|---|
| `∧` | `infixr:36` (`Operators.lean:31`) | `And`, infixr:35 | precedence differs | **1.36s** (flat; succeeds) |
| `∨` | `infixr:30` (`Operators.lean:38`) | `Or`, infixr:30 | **exact** | **46.3s**, timeout surfaces only at walk end |
| `→` | `infixr:25` (`Operators.lean:45`) | function arrow, infixr:25 | **exact** | **46.5s**, same |
| `↔` | `infixr:20` (`Operators.lean:52`) | `Iff`, infixr:20 | exact (latent) | not measured; `↔` chains do not occur in practice |
| `¬` | `notation:max "¬" p:40` | core `Not`, identical shape | exact (latent) | negligible (nesting depth ≤3 in practice) |

`HasAnd`'s off-by-one precedence (36 vs 35) is the *existing in-tree proof* that the offset kills
the exponential: `∧`-chains are flat and single uses resolve correctly. The fix below just makes
`→` and `∨` follow the pattern `∧` already uses.

---

## 4. Experimental record

All experiments in a dedicated git worktree of `task-619-phase8-wip` with a full copy of `.lake`
(main checkout untouched). Probe = `example : True → True → ... → True := by intros; trivial`
(resp. `∨`/`∧` with `by sorry`) inside `namespace Cslib.Logic.PL` after
`public import Cslib.Logics.Propositional.Defs`; baseline import cost ≈ 1.3-1.9s.

| # | Experiment | Result |
|---|---|---|
| E1 | truncated module (decls ≤240), migrated deps, `lake build` | terminates ~29s but **errors**: heartbeat timeout at `Scheme.lean:6255` + 2 knock-on kernel errors |
| E2 | E1 + `set_option diagnostics true` on `closed_unsat` | counters: `PropositionalConnectives.toHasImp ↦ 3180`, uniform `Coe* ↦ 2045`, `IBranch ↦ 37884` |
| E3 | arrow chains, branch deps, default heartbeats | n=4: 1.5s; n=8: 1.6s; n=12: 2.7s; n=16: 12.5s then 200000-heartbeat timeout |
| E4 | arrow chains, **pre-migration deps** (Connectives+Defs reverted, rebuilt) | n=8: 1.9s; n=16: 3.2s; n=24: **2.3s — flat** |
| E5 | arrow chains, branch deps, `maxHeartbeats 1000` | n=16: 1.9s; n=20: 4.3s; n=24: **46.5s** — runtime 2^n, unbounded by budget; timeout error surfaces only at end |
| E6 | `∨` chains, branch deps, hb=1000 | n=20: 4.1s; n=24: 46.3s — same as `→` |
| E7 | `∧` chains, branch deps | n=20, n=24: 1.35-1.36s — flat, succeeds under hb=1000 |
| E8 | **fix applied** (`→`→26, `∨`→31 in worktree Operators.lean), rebuild, re-run E5/E6 probes | n=24 arrows: **1.6s**; n=24 `∨`: **1.55s** — blowup eliminated |
| E9 | fix: formula-level sanity (`Proposition` args) | `a ∧ b ∨ c → a ∨ (b → c)` elaborates; `(a ∧ b ∨ c → a) = HasImp.imp (HasOr.or (HasAnd.and a b) c) a := rfl` and `(a → b → c) = a.imp (b.imp c) := rfl` both pass — grouping and defeq-to-constructor unchanged |
| E10 | fix: full `Scheme.lean` module `lake build` | **success, 29s** (933/933 jobs; was: >34min non-completion) |
| E11 | fix: full-library `lake build` on the branch worktree | **success, 3331/3331 jobs, 6m55s** — including `Cslib` (the barrel broken on main) |
| E12 | fix + LoopChecking band-aid removed (`set_option maxHeartbeats 1000000` block deleted) | module builds green at the default 200000 budget, 13.5s |

Reproduction commands are one-liners over the worktree; the probe generator and all probe files
are in the session scratchpad (`arr*.lean`, `or*.lean`, `and*.lean`, `formula-sanity.lean`).

---

## 5. The fix (executable recipe)

**File**: `Cslib/Foundations/Logic/Operators.lean` (on branch `task-619-phase8-wip`)

1. Line 38: `scoped infixr:30 " ∨ " => HasOr.or` → `scoped infixr:31 " ∨ " => HasOr.or`
2. Line 45: `scoped infixr:25 " → " => HasImp.imp` → `scoped infixr:26 " → " => HasImp.imp`

That is the entire fix. No changes to `Scheme.lean`, `Defs.lean`, `Connectives.lean`, class
declarations, instances, or bridge lemmas.

**Why it is safe** (each point verified):
- Relative precedence order within the operator family is preserved:
  `¬`(40) > `∧`(36) > `∨`(31) > `→`(26) > `↔`(20) mirrors the old 40/36/30/25/20 and core's
  40/35/30/25/20 — so every pure-formula expression parses to the same tree (E9 `rfl` tests).
- No other notation in the repo occupies precedence 26 or 31 with an interacting token
  (repo-wide grep over `infix`/`notation` at 24-27 and 30-32: only CLL's `⅋`/`&`/`⊸` on a
  different formula type, and `→₀`/`↾₀` on `FinFun` — different tokens, non-mixing types).
- Single-occurrence ambiguity (`A → B` still has two full-length parses at 26 vs 25) remains a
  constant-cost 2-way choice resolved by types — identical to the situation `∧` (36 vs 35) has
  always been in, everywhere, without incident.
- Upstream divergence is two characters in a file this fork already owns as part of the
  reconciliation; the same change is a candidate upstream PR since the collision penalizes any
  upstream `Cslib.Logic.*` code with Prop-level implication chains.

**Follow-through in the same phase-8 landing** (recommended, not required for green):
- `Cslib/Logics/Modal/Tableau/LoopChecking.lean:1206` — phase 8 added
  `set_option maxHeartbeats 1000000` with a comment attributing the slowdown to
  "a typeclass-projection layer that `isDefEq` must unfold". That attribution is the same
  misdiagnosis this report refutes; the actual cost is the `→`/`∨` ambiguity tax on that lemma's
  motive. **Verified (E12)**: with the precedence fix in place, deleting the whole 5-line
  `set_option` block leaves the module building green at the default 200000-heartbeat budget
  (13.5s). Phase 8 should drop the band-aid and its misattributing comment.
- `Connectives.lean`'s "Standing Invariant: Notation Collision Risk" docstring should gain one
  sentence: *exact* token+precedence collision with a core notation causes exponential
  choice-node backtracking on nested chains (this incident), so any future scoped notation in
  `Cslib.Logic` must avoid exact-collision with core `→`/`∨`/`↔`/`¬`/`∧` precedences. The `↔`
  (20 vs 20) and `¬` (identical shape) latent collisions are acceptable today only because no
  chains occur; do not register `HasIff`/`HasNot` instances without revisiting (the docstring
  already forbids this for the Ambiguous-term reason; this adds the performance reason).

**What the fix is NOT**: no `@[reducible]`/`@[irreducible]` attributes, no instance-priority
changes, no `set_option maxHeartbeats` anywhere, no `simp` lemma additions, no restoration of the
deleted `Defs.lean` notations, no `Scheme.lean` edits. The prior report's suggested remedies 2-4
(instance reducibility, rewriting connective occurrences, splitting the lemma) are all
unnecessary and would not have fixed the actual mechanism (the blowup occurs in statements whose
`→`s are plain function arrows, before instances are ever relevant).

---

## 6. Zero-debt compliance

- The fix introduces no `sorry`, no axioms, no deferred work.
- All measurements above were actually run in this session; nothing is extrapolated except the
  explicit 2^29 runtime estimate (labeled as such), which is bounded on both sides by measured
  2^20/2^24 data and the observed >34min/>400s behavior.

## 7. CSLib reuse check

Not applicable in the usual sense (no new definitions or abstractions are recommended — the fix
is two precedence digits in an existing file). Checked that no existing CSLib
typeclass/notation facility provides a collision-free arrow already: `Operators.lean` is the
single source of `→`-on-formulas notation post-phase-8, so it is also the single correct fix
site.

## 8. Full-library gate (completed)

`lake build` (whole default target) on the branch worktree with the fix:
**Build completed successfully (3331 jobs)** in 6m55s wall / 52m CPU, including
`Cslib` (the top-level barrel, job 3330/3331) — i.e. the phase-8 branch plus this two-character
fix produces a fully green library, repairing the barrel that is broken on `main`. Additionally,
the `LoopChecking.lean` heartbeat band-aid was deleted and that module rebuilt green at the
default budget (E12), so phase 8 can land without it.

The verified worktree (branch `task-619-phase8-wip` + the two-line `Operators.lean` change + the
band-aid removal) lives at the session scratchpad path `scratchpad/wt` for the implementer's
reference this session; the durable recipe is section 5 (it is two precedence digits plus one
5-line deletion). After this session the worktree can be dropped with
`git worktree remove --force <path>` / `git worktree prune`.

---

## Adversarial Self-Verification

| Claim | Source/Counterexample | Verdict |
|---|---|---|
| The runaway is NOT kernel defeq (refutes prior report §4) | E5: with `maxHeartbeats 1000`, runtime still scales 2^n and the *deterministic timeout error* eventually surfaces from the elaborator (`timeout at 'elaborator'/'isDefEq'/'whnf'`) — kernel work would never produce a heartbeat error at all; E1 shows the sibling failure at `Scheme.lean:6255` is a plain elaborator heartbeat timeout | CONFIRMED (prior claim refuted) |
| Heartbeat budget cannot bound the walk (explains "40000 → no timeout in 400s") | E5 measured: budget 1000 (≈0.1s of work if binding) yet n=24 runs 46.5s before erroring; swallowing mechanism located at `src/lean/Lean/Elab/App.lean:1939` (`observing` per alternative) + `App.lean:2062` (choice fold), v4.33.0-rc1 toolchain source read directly | CONFIRMED |
| Collision is precedence-exactness, not typeclass indirection per se | E7 vs E6: `∧` (HasAnd, *has* instance+projection indirection, precedence 36≠35) is flat; `∨` (30=30) and `→` (25=25) blow up. If projection unfolding were the cost, `∧` would blow up too | CONFIRMED |
| Pre-migration flatness | E4 control in the same worktree (only Connectives.lean+Defs.lean reverted, deps rebuilt): 24-arrow chain flat at 2.3s | CONFIRMED |
| Decl 241's trigger term is the 29-arrow `suffices key` at `Scheme.lean:8410` | Arrow count measured (29 `→` tokens in the single term); per-alternative rate from E5 extrapolates 2^29 to 25-50min matching the >34min observation; adversarial alternative "some other term in the decl is the payer" — no other term in decl 241 has >4 chained arrows (inspected); the 22 lemma hypotheses are parenthesized binders (no `→` tokens) | CONFIRMED (extrapolation labeled) |
| `intExpandBranches_closed_unsat` (line 6264) also fails, contradicting prior report's "≤240 builds clean" | E1 reproduced twice (probe + real truncated `lake build`): deterministic 200000-heartbeat timeout at 6255 + knock-on kernel unknown-constant errors at 6926/6993 | CONFIRMED |
| Why the full-file build shows *no* error output | Lake flushes a module's log on module completion; decl 241 never completes, so 6255's error is never displayed. Verified behaviorally (truncated build displays it; full build displays nothing) | CONFIRMED |
| The two-character precedence fix eliminates the blowup | E8: 46.5s→1.6s (arrows), 46.3s→1.55s (`∨`); E10: full Scheme module 29s green | CONFIRMED |
| The fix does not change formula parsing/semantics | E9: grouping test `a ∧ b ∨ c → a ∨ (b → c)` elaborates; two `rfl` equations pin the parse to the same constructor terms as before; relative precedence order preserved (40>36>31>26>20 ≅ 40>36>30>25>20); repo grep found no interacting notation at 26/31 | CONFIRMED |
| Adversarial: could restoring Defs.lean's old notations (with priority) fix it instead? | No — the blowup occurs at *Prop*-level arrows (e.g. `True → True` probes, closed_unsat's chain), where Proposition notations are irrelevant; the collision to remove is HasImp-vs-core-arrow. Prior report §5.2 additionally showed plain restoration causes Ambiguous-term errors | CONFIRMED (alternative rejected with evidence) |
| Adversarial: could the earlier 4.6s `∧` measurement (later re-measured 1.35s) invalidate E7? | Re-ran after warm-up: 1.35s at n=20 and 1.36s at n=24 — the first run paid one-time rebuild/cache cost. n-independence (20 vs 24 identical) is the load-bearing observation | CONFIRMED (measurement artifact identified and corrected) |
| Reference grounding tier | Tier 3 (implementation-backed): grounded in git diffs (`main..1e88ad3e`), Lean toolchain sources (v4.33.0-rc1 `src/lean/Lean/Elab/App.lean`), and 11 experiments run this session. No literature source is cited; no BibKey applicable (`references.bib` not implicated) | N/A — no Tier 1 claims |

**Uncertain claims, with confidence**:
- Exact internal shape of the parser's choice-node emission (per-level nesting vs merged
  alternatives): not directly inspected; ~85% confidence in the per-level description. Immaterial
  to the fix — the 2^n *measurement* and its elimination are direct.
- The 2^29 ≈ 25-50min figure: extrapolation from measured 2^20/2^24 points; ±2× machine-load
  variance. The qualitative conclusion (walk ≫ 400s observation window) is robust.
