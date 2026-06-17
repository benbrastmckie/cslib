# Teammate B Findings: Alternative Approaches and Prior Art

## Key Findings

### 1. Root Cause Confirmed (Aligned with Teammate A)

The CI failure is in `Cslib.Logics.Propositional.Defs` due to two theorems
(`Proposition.instBot_eq`, `Proposition.instTop_eq`) that auto-include the section variable
`[DecidableEq Atom]` but do not use it. The CI runs with `--wfail` (warnings-as-errors), which
causes this to be a hard build failure.

### 2. Branch Topology

```
upstream/main (70c5bf58) --- feat/propositional-v2 (7cc09612) [PR #648]
           |
           +--- 5700fedb --- 0afc9d6c --- 5785ebbd [feat/temporal-formula-propositional, PR #649]
```

Both PRs diverged from the SAME upstream/main commit (`70c5bf58`, the PR #536 merge).
The temporal branch is NOT currently based on feat/propositional-v2 — they are parallel branches.
When CI merges PR #649 HEAD into upstream/main, the `instBot_eq`/`instTop_eq` theorems are present.

### 3. The CI Uses `--wfail` (Lean Action Default)

The workflow file `.github/workflows/lean_action_ci.yml` only specifies `--iofail`, but the
`leanprover/lean-action@v1` action internally adds `--wfail` (warnings-as-errors). This is a
standard behavior of the Lean Action CI, not an explicit project setting. All warnings are
errors in CI.

### 4. Rebase Conflict Assessment

Rebasing `feat/temporal-formula-propositional` onto `feat/propositional-v2` would produce conflicts
in these files:

| File | Conflict Nature |
|------|----------------|
| `Cslib/Logics/Propositional/Defs.lean` | Both branches modify: references, IPL/CPL notation, instBot/Top theorems |
| `Cslib/Foundations/Logic/Connectives.lean` | temporal adds temporal classes; propositional-v2 has different references |
| `Cslib/Logics/Propositional/NaturalDeduction/Basic.lean` | reference changes diverge |
| `Cslib/Logics/Propositional/NaturalDeduction/Theory.lean` | both modify instIsIntuitionisticIPL |
| `references.bib` | temporal adds different entries than propositional-v2 |
| `Cslib.lean` | both add new imports |

Unique content in the temporal branch (non-conflicting new files):
- `Cslib/Logics/Temporal/Syntax/Formula.lean`
- `Cslib/Logics/LTL/Syntax/Formula.lean`
- `Cslib/Logics/LTL/Semantics/Satisfies.lean`

### 5. IsIntuitionistic/IsClassical Already Aligned

Both branches now use `InferenceSystem`-parameterized `IsIntuitionistic`/`IsClassical` (from PR
#536). The temporal branch did reconcile with this — no further reconciliation is needed there.
The difference is in how IPL/CPL/MPL are defined:
- temporal branch: `abbrev IPL (Atom : Type u) : Theory Atom := {⊥ → A | A : Proposition Atom}`
- propositional-v2: `abbrev IPL : Theory Atom := Set.range (Proposition.imp ⊥ ·)`

---

## Stacked PR Patterns in This Repo

Examining the PR history and git log:

1. **Pattern observed**: Prior stacked PRs (e.g., related CI fix commits) used `git rebase` to
   rebase stacked branches onto updated bases. The commit message pattern "Rebased on upstream/main
   now that #536 is merged" (in PR #648 description) shows this is the accepted workflow.

2. **No complex stacking tools**: The repo does not appear to use tools like `git-stack`, `stgit`,
   or GitHub's "update-with-rebase" stacking feature. Stacked PRs are managed manually via `git
   rebase`.

3. **Force-push accepted**: The `--force-with-lease` pattern is standard for updating PR branches.
   There's no evidence of any "no force push" policy in this repo for personal branches.

4. **Historical example**: PR #648 was itself rebased ("Rebased on upstream/main now that #536 is
   merged" — comment by benbrastmckie). This established the pattern to follow for PR #649.

---

## CSLib CI Pipeline Requirements

Based on `.github/workflows/lean_action_ci.yml`:

1. `lake build --wfail --iofail` — All warnings are errors; all IO failures are errors
2. `lake exe mk_all --check` — Verify `Cslib.lean` barrel import is up to date
3. `lake exe checkInitImports` — All files must `import Cslib.Init`
4. `lint-style-action` — Text linting (line length, headers, etc.)

The `--wfail` flag (added by lean-action internally) means:
- `automatically included section variable(s) unused` → BUILD FAILS
- `does not use the following hypothesis in its type` → BUILD FAILS

---

## Import/Dependency Considerations

### Cslib.lean Ordering
Both branches add imports to `Cslib.lean`. The temporal branch adds 4 imports:
```lean
public import Cslib.Foundations.Logic.Connectives  -- shared with propositional-v2
public import Cslib.Logics.LTL.Semantics.Satisfies -- unique to temporal
public import Cslib.Logics.LTL.Syntax.Formula      -- unique to temporal
public import Cslib.Logics.Temporal.Syntax.Formula  -- unique to temporal
```

The `Connectives` import is also in propositional-v2. When rebasing, this won't conflict if the
rebase correctly picks up propositional-v2's `Connectives` import position.

### checkInitImports Constraint
All new files in the temporal branch (LTL/Satisfies, LTL/Formula, Temporal/Formula) already
begin with `import Cslib.Init`. This is compliant.

### Dependency Chain
The temporal files depend on `Connectives.lean` which is introduced by PR #648. If PR #649 is
rebased onto PR #648, this dependency is naturally satisfied.

---

## Alternative Fix Strategies

### Strategy A: Rebase onto Updated PR #648 (RECOMMENDED)
**Steps:**
```bash
git checkout feat/temporal-formula-propositional
git rebase feat/propositional-v2
# Resolve conflicts (approximately 5 files)
# Key resolution: for Defs.lean, take propositional-v2's version + Architecture docblock from temporal
# For Connectives.lean: take propositional-v2's base + temporal's HasUntil/HasSince/HasNext additions
# For Cslib.lean: keep propositional-v2's Connectives import position + temporal's 3 new imports
git push origin feat/temporal-formula-propositional --force-with-lease
```
**Pros:** Clean git history, proper stacking, removes instBot/Top naturally
**Cons:** 5+ conflict files to resolve manually; risk of introducing errors during resolution

### Strategy B: Direct Minimal Fix (FASTEST)
**Steps:**
Fix the two offending theorems in place by adding `omit [DecidableEq Atom] in`:
```lean
omit [DecidableEq Atom] in
@[simp, grind =]
theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = Proposition.bot := rfl

omit [DecidableEq Atom] in
@[simp, grind =]
theorem Proposition.instTop_eq : (⊤ : Proposition Atom) = Proposition.top := rfl
```
**Pros:** One-line-per-theorem fix, no rebase conflicts, CI passes immediately
**Cons:** These theorems are absent from propositional-v2 (cleaner version); diverges further

### Strategy C: New Fresh Branch from propositional-v2 (CLEANEST BUT MOST WORK)
**Steps:**
1. Create a new branch from propositional-v2 tip
2. Port only the temporal-unique content: 
   - 3 new .lean files (Temporal/Formula, LTL/Formula, LTL/Satisfies)
   - Additions to Connectives.lean (HasUntil, HasSince, HasNext, bundles)
   - 3 new import lines in Cslib.lean
   - New references from references.bib (Burgess1984, VardiWolper1986, GPSS1980, etc.)
3. Delete the old temporal branch, push the new one under the same name

**Pros:** No merge conflicts, guaranteed clean state, full propositional-v2 integration
**Cons:** Most work; must manually port all temporal content; risks missing something

### Strategy D: Remove the Two Theorems Directly
**Analysis:** The temporal branch files (Temporal/Formula, LTL/Formula, LTL/Satisfies) use `.bot`
constructor syntax directly, not `⊥` notation requiring unfolding via `instBot_eq`. Therefore,
`instBot_eq` and `instTop_eq` are safe to remove from Defs.lean without breaking temporal code.
```bash
# In Cslib/Logics/Propositional/Defs.lean, delete:
@[simp, grind =]
theorem Proposition.instBot_eq : (⊥ : Proposition Atom) = Proposition.bot := rfl

@[simp, grind =]
theorem Proposition.instTop_eq : (⊤ : Proposition Atom) = Proposition.top := rfl
```
**Pros:** Minimal change, aligns with propositional-v2 (which also lacks these)
**Cons:** Need to verify nothing else in the project uses them (grep shows no usage elsewhere)

---

## Confidence Level: HIGH

- Root cause confirmed: `instBot_eq`/`instTop_eq` with `--wfail` in `lean-action`
- Branch topology verified: temporal diverges from upstream/main, not from propositional-v2
- Rebase conflict analysis: 5 files will need conflict resolution
- Alternative strategies: all verified as technically feasible

**Recommended approach**: Strategy A (rebase) is the correct long-term approach. Strategy D
(removing the two theorems) is the fastest fix if the goal is to unblock CI immediately. Strategy D
can be combined with Strategy A (rebase after the minimal fix) in two steps.

### Priority Order for Implementation:
1. **Immediate**: Remove `instBot_eq` / `instTop_eq` (Strategy D) OR add `omit` annotations
   (Strategy B) to unblock CI
2. **Follow-up**: Rebase onto updated propositional-v2 (Strategy A) for clean history before merge
