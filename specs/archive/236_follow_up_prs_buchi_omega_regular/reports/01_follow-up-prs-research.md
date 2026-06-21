# Research Report: Follow-up PRs from PR #649

**Task**: 236 -- Complete follow-up PRs from PR #649 for Buchi automata and closure of omega-regular languages under boolean operations

**Session**: sess_1781835768_ac3571

---

## 1. PR #649 Context and Follow-up Items

PR #649 ("feat(Logics/LTL): LTL formula type and semantics over omega-words") is an open PR on `leanprover/cslib` (branch `feat/temporal-formula-propositional`, state: OPEN, merge status: BLOCKED). It adds:

- `Cslib/Foundations/Logic/Connectives.lean` -- typeclass hierarchy (`HasUntil`, `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`)
- `Cslib/Logics/LTL/Syntax/Formula.lean` -- LTL formula inductive type with `{atom, bot, imp, next, untl}`
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` -- satisfaction over omega-words `v : N -> (Atom -> Prop)`

The key follow-up comment (comment ID 4715486412, by benbrastmckie, 2026-06-16) identifies **four follow-up items**:

### Follow-up Item 1: LTL satisfaction over OmegaExecution

> "Connection to `LTS.OmegaExecution` -- which already carries both `ss : omegaSequence State` and `mus : omegaSequence Label` -- is the right approach. A follow-up PR can define satisfaction directly over `OmegaExecution` pairs rather than bare state sequences."

**Status**: Not started. `Satisfies.lean` currently uses `v : N -> (Atom -> Prop)`. An `OmegaExecution`-based satisfaction would tie LTL directly to the LTS framework.

### Follow-up Item 2: LTL-to-Buchi translation theorem

> "A natural follow-up is to prove the LTL-to-Buchi translation theorem, connecting `LTL.Satisfies` to `omegaLanguage.IsRegular` via the existing boolean closure results."

**Status**: Not started. This is the Vardi-Wolper (1986) automata-theoretic approach: given an LTL formula phi, construct an NBA that accepts exactly the omega-words satisfying phi.

### Follow-up Item 3: Encodable/Countable/Infinite/Denumerable instances

> "Removed. Deferred to a completeness PR where they are actually needed."

**Status**: Deferred. These would be needed for an LTL completeness proof. Not relevant to the Buchi automata / omega-regular language scope.

### Follow-up Item 4: LTL/Temporal separation

From the subsequent discussion (comment ID 4744075043), benbrastmckie explains:
> "It would make sense to separate this embedding into `LTL/Embedding.lean` so that `LTL/` is self-contained and does not transitively depend on `Temporal/`."

**Status**: Not started. Currently `LTL/Syntax/Formula.lean` imports `Temporal/Syntax/Formula.lean` for `Formula.toTemporal`. Separating the embedding would decouple the two logics.

---

## 2. Existing Codebase Inventory

### 2.1 Buchi Automata (Fully Developed)

CSLib has a mature Buchi automata library authored primarily by Ching-Tsun Chou:

| File | Content |
|------|---------|
| `Cslib/Computability/Automata/NA/Basic.lean` | `NA.Buchi` structure (nondeterministic), `NA.Muller` structure |
| `Cslib/Computability/Automata/DA/Basic.lean` | `DA.Buchi` structure (deterministic), `DA.Muller` structure |
| `Cslib/Computability/Automata/DA/Buchi.lean` | `buchi_eq_finAcc_omegaLim`: DA Buchi language = omega-limit of FinAcc language |
| `Cslib/Computability/Automata/NA/BuchiInter.lean` | Intersection of two NBAs (product + toggle history state) |
| `Cslib/Computability/Automata/NA/BuchiEquiv.lean` | Reindexing equivalence for NBAs |
| `Cslib/Computability/Automata/NA/Sum.lean` | Union of indexed family of NAs |
| `Cslib/Computability/Automata/NA/Concat.lean` | Concatenation of FinAcc with NA |
| `Cslib/Computability/Automata/NA/Loop.lean` | Omega-power loop construction |
| `Cslib/Computability/Automata/NA/Pair.lean` | Pair language constructions |

### 2.2 Omega-Regular Language Closure (Complete)

`OmegaRegularLanguage.lean` already proves closure of omega-regular languages under **all** boolean operations:

| Theorem | Statement |
|---------|-----------|
| `IsRegular.bot` | Empty language is omega-regular |
| `IsRegular.top` | Full language is omega-regular |
| `IsRegular.sup` | Union of two omega-regular languages is omega-regular |
| `IsRegular.inf` | Intersection of two omega-regular languages is omega-regular |
| `IsRegular.compl` | **Complement** of omega-regular language is omega-regular (via Buchi congruence) |
| `IsRegular.iSup` | Finite union of omega-regular languages is omega-regular |
| `IsRegular.iInf` | Finite intersection of omega-regular languages is omega-regular |
| `IsRegular.hmul` | Concatenation of regular + omega-regular is omega-regular |
| `IsRegular.omegaPow` | Omega-power of regular language is omega-regular |
| `IsRegular.regular_omegaLim` | Omega-limit of regular language is omega-regular |
| `IsRegular.eq_fin_iSup_hmul_omegaPow` | Characterization: omega-regular iff finite union of L * M^omega |
| `IsRegular.fin_cover_saturates` | Saturation cover closure |
| `IsRegular.not_da_buchi` | There exists an omega-regular language not accepted by any DA Buchi |

**KEY FINDING**: The boolean closure results for omega-regular languages are **already complete**. The `IsRegular.compl` theorem uses the Buchi congruence approach (Ramsey-theoretic). The `proof_wanted` McNaughton theorem (`IsRegular.iff_da_muller`) is declared but not yet proved.

### 2.3 Supporting Infrastructure

| File | Content |
|------|---------|
| `OmegaLanguage.lean` | `omegaLanguage` type, algebra (`hmul`, `omegaPow`, `omegaLim`, `map`), extensive algebraic properties |
| `RegularLanguage.lean` | `Language.IsRegular` characterizations via DA/NA, closure under complement, union, intersection, concat, Kleene star |
| `BuchiCongruence.lean` | Buchi congruence relation, saturation cover, used for complementation proof |
| `OmegaSequence/Temporal.lean` | `Step`, `LeadsTo`, `leadsTo_trans`, `leadsTo_cases_or` -- temporal reasoning primitives used in Buchi intersection proofs |
| `OmegaSequence/InfOcc.lean` | `infOcc` (infinitely occurring set), used in Muller acceptance |
| `LTS/OmegaExecution.lean` | `OmegaExecution` carrying `ss : omegaSequence State` and `mus : omegaSequence Label`, with `extract_execution`, `flatten_execution`, etc. |

### 2.4 LTL Files (from PR #649, on main)

Both files are already on main:
- `Cslib/Logics/LTL/Syntax/Formula.lean` -- LTL formula type with `LTLConnectives` instance, `toTemporal` embedding
- `Cslib/Logics/LTL/Semantics/Satisfies.lean` -- basic satisfaction `Satisfies v i phi` over `v : N -> (Atom -> Prop)`

---

## 3. Analysis: What Needs to Be Done

### 3.1 Follow-up A: LTL Satisfaction over OmegaExecution

**Goal**: Define `LTL.Satisfies` directly over `LTS.OmegaExecution` pairs rather than bare state sequences.

**What exists**:
- `LTS.OmegaExecution lts ss mus` requires `forall i, lts.Tr (ss i) (mus i) (ss (i + 1))`
- Current `LTL.Satisfies v i phi` uses `v : N -> (Atom -> Prop)`

**What's needed**:
1. A new file `Cslib/Logics/LTL/Semantics/OmegaExecution.lean` (or similar) defining:
   ```lean
   def LTL.SatisfiesExec (lts : LTS State Label) (labeling : State -> (Atom -> Prop))
       (ss : omegaSequence State) (mus : omegaSequence Label) (i : N) (phi : LTL.Formula Atom) : Prop
   ```
   or equivalently a wrapper that lifts `Satisfies` via `v := labeling . ss`.
2. A proof that `SatisfiesExec` agrees with `Satisfies` when the labeling is derived from an OmegaExecution.
3. This connects the LTL semantics to the existing LTS machinery.

**Complexity**: Low-medium. The core is a definitional bridge; the interesting part is ensuring the types line up correctly with `OmegaExecution`.

### 3.2 Follow-up B: LTL-to-Buchi Translation (Vardi-Wolper)

**Goal**: Prove that for every LTL formula phi, there exists an NBA accepting exactly the omega-words satisfying phi. This implies that the set of omega-words satisfying any LTL formula is omega-regular.

**What exists**:
- `omegaLanguage.IsRegular` defined as existence of a finite-state NBA
- All boolean closure results for omega-regular languages
- NBA constructions: union (`Sum`), intersection (`BuchiInter`), concatenation (`Concat`), loop (`Loop`)
- `LTL.Satisfies` semantics

**What's needed**:
This is the main theorem:
```lean
theorem LTL.IsRegular (phi : LTL.Formula Atom) [Finite Atom] :
    { v : omegaSequence (Atom -> Prop) | LTL.Satisfies v 0 phi }.IsRegular
```

The standard proof proceeds by structural induction on phi:
- **Base case (atom p)**: The language `{v | v 0 p}` is omega-regular (simple 1-state NBA)
- **Bot**: Empty language is omega-regular (already proved: `IsRegular.bot`)
- **Imp (phi psi)**: By IH, `L_phi` and `L_psi` are omega-regular. `L_{phi -> psi} = L_phi^c cup L_psi`, which is omega-regular by complement + union closure (already proved)
- **Next (phi)**: If `L_phi` is omega-regular, then `L_{X phi}` (shift by 1) is omega-regular. This requires constructing an NBA for the shifted language.
- **Until (psi phi)**: This is the hardest case. The standard construction uses an "on-the-fly" NBA that tracks obligations. Alternative: use the equivalence between LTL and first-order logic over omega-words, combined with the existing closure results.

**Complexity**: High. The `until` case is non-trivial and is the core of the Vardi-Wolper construction. The "shift" construction for `next` also requires new work. However, since all boolean closure results exist, the propositional cases are straightforward.

**Key challenge**: The existing `Satisfies` uses `v : N -> (Atom -> Prop)` (a valuation function), but `omegaLanguage.IsRegular` works with `omegaSequence Symbol`. These need to be bridged: the "alphabet" for the NBA would be `Set Atom` (or `Atom -> Prop` with appropriate finiteness), and the omega-word `v` is reinterpreted as an `omegaSequence (Set Atom)`.

### 3.3 Follow-up C: LTL/Temporal Decoupling

**Goal**: Move `Formula.toTemporal` from `LTL/Syntax/Formula.lean` to a separate `LTL/Embedding.lean` so `LTL/` does not transitively depend on `Temporal/`.

**What exists**:
- `LTL/Syntax/Formula.lean` currently imports `Cslib.Logics.Temporal.Syntax.Formula`
- The only use of the import is the `Formula.toTemporal` function

**What's needed**:
1. Create `Cslib/Logics/LTL/Embedding.lean` containing `Formula.toTemporal`
2. Remove `import Cslib.Logics.Temporal.Syntax.Formula` from `LTL/Syntax/Formula.lean`
3. Update `Cslib.lean` barrel import

**Complexity**: Low. This is a pure refactoring task.

### 3.4 Follow-up D: McNaughton's Theorem (proof_wanted)

**Goal**: Prove `IsRegular.iff_da_muller`: an omega-language is omega-regular iff it is accepted by a finite-state deterministic Muller automaton.

**What exists**:
- `DA.Muller` and `NA.Muller` structures with acceptance conditions
- `proof_wanted IsRegular.iff_da_muller` in `OmegaRegularLanguage.lean`
- The forward direction (NBA -> DMA) requires the Safra construction or similar
- The backward direction (DMA -> NBA) is simpler

**Complexity**: Very high. The Safra construction (or Muller-Schupp / LAR construction) is technically intricate. This is a major formalization effort.

---

## 4. Scope Determination

Based on the PR #649 comment, the task description focuses on "Buchi automata and closure of omega-regular languages under boolean operations." Given that the boolean closure results are **already complete**, the task should be scoped to the follow-up items that connect LTL to the automata-theoretic framework.

**Recommended scope for this task (3 follow-up PRs)**:

### PR 1: LTL/Temporal Decoupling (Follow-up C)
- Move `toTemporal` to `LTL/Embedding.lean`
- Remove `Temporal` dependency from `LTL/Syntax/Formula.lean`
- Smallest PR, no new theorems

### PR 2: LTL Satisfaction over OmegaExecution (Follow-up A)
- New file `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean`
- Bridge `Satisfies` to `OmegaExecution` via labeling function
- Proof of equivalence

### PR 3: LTL-to-Buchi Translation (Follow-up B)
- Core theorem: every LTL formula defines an omega-regular language
- Structural induction using existing closure results
- New NBA constructions for atom, next, and until cases
- This is the substantial PR

**Out of scope**: McNaughton's theorem (Follow-up D) -- too complex for this task, and the `proof_wanted` suggests it is a standalone research problem. The Encodable/Countable instances (Follow-up Item 3) are deferred to a completeness task.

---

## 5. Key Design Decisions

### 5.1 Alphabet Type for LTL-to-Buchi

The critical design question for PR 3 is the alphabet type. Options:

**Option A**: `Symbol = (Atom -> Prop)` (current `Satisfies` approach)
- Pro: Directly matches `Satisfies v i`
- Con: `Atom -> Prop` is not finite even when `Atom` is finite

**Option B**: `Symbol = Set Atom` with `[Fintype Atom]`
- Pro: `Set Atom` is `Fintype` when `Atom` is, matching `IsRegular`'s finite-state requirement
- Con: Need to convert between `Set Atom` and `Atom -> Prop`

**Option C**: `Symbol = (Atom -> Bool)` with `[Fintype Atom]`
- Pro: Computationally concrete, `Fintype` automatically
- Con: Decidability assumption on atom truth

**Recommendation**: Option B (`Set Atom` with `[Fintype Atom]`) is the standard approach in automata theory literature and aligns with the Vardi-Wolper paper. The conversion between `Set Atom` and `Atom -> Prop` is straightforward via membership.

### 5.2 Until Case Strategy

For the `until` case in the LTL-to-Buchi translation, two approaches:

**Approach 1**: Direct construction (Vardi-Wolper style)
- Build an NBA whose states track "obligations" (which until-subformulas are waiting)
- States are subsets of the Fischer-Ladner closure of the formula
- Technically involved but well-documented in literature

**Approach 2**: Leverage existing closure results
- `phi U psi` can be expressed as: `psi or (phi and X(phi U psi))`
- This gives a fixed-point characterization
- The omega-regularity follows from the closure under union, intersection, and the next-step shift
- Requires showing that the fixed-point is the least fixed point and that it is omega-regular

**Recommendation**: Approach 2 is more natural in the CSLib context since all closure results exist. The key new construction is the "shift" NBA for the `next` operator.

---

## 6. Dependency Graph

```
PR 1 (LTL/Temporal Decoupling)
  |
  v
PR 2 (LTL over OmegaExecution)  -- depends on PR 1 only if it uses LTL/Syntax/Formula.lean
  |
  v
PR 3 (LTL-to-Buchi)  -- depends on PR 2 (needs Satisfies), and existing OmegaRegularLanguage.lean
```

PR 1 and PR 2 are largely independent (PR 2 does not need the decoupling). PR 3 builds on the clean `Satisfies` definition from PR 2.

---

## 7. File Inventory for Implementation

### New files needed:

| File | PR | Content |
|------|-----|---------|
| `Cslib/Logics/LTL/Embedding.lean` | PR 1 | `Formula.toTemporal` moved here |
| `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` | PR 2 | Satisfaction over OmegaExecution |
| `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` | PR 3 | LTL-to-Buchi main theorem |

### Modified files:

| File | PR | Change |
|------|-----|--------|
| `Cslib/Logics/LTL/Syntax/Formula.lean` | PR 1 | Remove Temporal import, remove `toTemporal` |
| `Cslib.lean` | PR 1-3 | Add new module imports |

### Existing files used (read-only):

| File | Used by |
|------|---------|
| `Cslib/Computability/Languages/OmegaRegularLanguage.lean` | PR 3 (closure results) |
| `Cslib/Computability/Automata/NA/Basic.lean` | PR 3 (NBA structure) |
| `Cslib/Foundations/Semantics/LTS/OmegaExecution.lean` | PR 2 |
| `Cslib/Foundations/Logic/Connectives.lean` | All PRs |

---

## 8. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| `until` case in LTL-to-Buchi may require complex NBA construction | High | Use fixed-point approach leveraging existing closure results |
| Alphabet type mismatch between `Satisfies` and `IsRegular` | Medium | Use `Set Atom` with `[Fintype Atom]`, provide explicit conversion |
| PR #649 still open -- LTL files may change | Low | LTL files are already on main branch; PR changes are isolated to LTL content |
| McNaughton's theorem out of scope but related | Low | Clearly mark as separate future work |
| Finiteness constraints for NBA state spaces | Medium | Need `[Fintype Atom]` or `[Finite Atom]` assumption |

---

## 9. Recommendations

1. **Scope to three PRs** as outlined above (decoupling, OmegaExecution bridge, LTL-to-Buchi)
2. **Start with PR 1** (decoupling) as it is mechanical and creates a cleaner foundation
3. **For PR 3**, use the fixed-point approach for `until` rather than the direct Vardi-Wolper tableau construction
4. **Require `[Finite Atom]`** for the LTL-to-Buchi theorem (standard in the literature)
5. **Leave McNaughton's theorem** as a separate task (it is already marked `proof_wanted`)
6. **Note**: The boolean closure results for omega-regular languages are already complete -- no new closure proofs are needed
