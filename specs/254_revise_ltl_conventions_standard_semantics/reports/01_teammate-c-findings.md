# Teammate C (Critic) Findings — Task 254

**Role**: Find gaps, risks, and things other researchers might miss.

---

## Key Findings

### 1. Main Branch Has a Docstring Bug, Not a Code Bug, in `untl` Arg Order

The task description says "change notation from Burgess convention (event U guard) to standard convention (guard U event)". However, the CODE in both branches uses identical arg order: `untl(φ₁=guard, φ₂=event)`.

What differs is the DOCSTRING:

- **Main** `Satisfies.lean`: `| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ`
  - Second arg (φ) is the event (witness at j), first arg (ψ) is the guard. Standard convention.
  - But the docstring says "Burgess convention: φ holds at the event, ψ at intermediate guard points" — **inverted from reality**.

- **Feature branch** `Satisfies.lean`: `| .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ`
  - Second arg (ψ) is the event (witness at j), first arg (φ) is the guard. Standard convention.
  - Docstring correctly says "guard U event".

- **Main** `Formula.lean`: `someFuture φ = .untl .top φ` — φ is the second arg (event), ⊤ is the first (guard). Correct code.
  - Docstring says "Burgess: event U guard", implying φ is first — **wrong**.

- **Feature branch** `Formula.lean`: `someFuture φ = .untl .top φ` — **identical code**. Docstring correctly says "guard U event: φ₁ holds until φ₂".

**Confirmation from Axioms.lean** (on main): BX2G is labelled "Guard monotonicity" = `HasUntil.untl φ χ → HasUntil.untl ψ χ` (first arg varies in G(φ→ψ), so first arg = guard). BX3 is "Event monotonicity" = `HasUntil.untl χ φ → HasUntil.untl χ ψ` (second arg varies, so second arg = event). The axioms confirm: `untl(guard, event)` is the convention on main.

**Risk**: The task description is slightly misleading — the arg order in CODE does not change. Only docstrings and notation symbols change.

### 2. `someFuture` Definition: Both Branches Have `.untl .top φ`

The task says "update someFuture from φ U ⊤ to ⊤ U φ". This is ambiguous:

- **Main** `Formula.lean`: `abbrev Formula.someFuture (φ) := .untl .top φ`  
  Docstring says "φ U ⊤" (Burgess) — but this corresponds to `.untl φ .top` if φ is first.  
  The CODE is `.untl .top φ` — top is first (guard), φ is second (event).

- **Feature branch** `Formula.lean`: `abbrev Formula.someFuture (φ) := .untl .top φ` — **identical**.  
  Docstring correctly says "⊤ U φ" meaning ⊤ is guard (first), φ is event (second).

**Conclusion**: The `someFuture` code does NOT change between branches. The task description's "from φ U ⊤ to ⊤ U φ" refers only to the DOCSTRING convention label, not to any code change.

### 3. Feature Branch Removes MORE Than the Task Description States (Connectives.lean)

The task says "remove HasSince/TemporalConnectives/BimodalConnectives". The feature branch also removes:
- `HasBox`
- `ModalConnectives`
- The `BimodalConnectives → ModalConnectives` bridge instance

**Feature branch Connectives.lean has only**:
`HasBot`, `HasImp`, `HasUntil`, `HasNext`, `HasAnd`, `HasOr`, `PropositionalConnectives`, `FutureTemporalConnectives`, `LTLConnectives`.

**Main Connectives.lean additionally has**:
`HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives` + bridge instance.

The task description does NOT say to remove `HasBox` or `ModalConnectives`. If the implementation follows only the task description, the result will DIFFER from the feature branch Connectives.lean. If it follows the feature branch exactly, it will break `ProofSystem.lean`, `Theorems/Modal/Basic.lean`, `Theorems/Modal/S5.lean`, and `Logics/Modal/Basic.lean` (all of which use `HasBox`).

### 4. Cslib.lean Diff is Massive and Mostly About Non-LTL Files

The feature branch removes from `Cslib.lean`:
- All `Cslib.Logics.Bimodal.*` imports (50+ lines)
- `Cslib.Foundations.Logic.Axioms`
- `Cslib.Foundations.Logic.ProofSystem`
- `Cslib.Foundations.Logic.Theorems.Modal.*`
- `Cslib.Foundations.Logic.Theorems.Temporal.*`
- `Cslib.Foundations.Logic.Metalogic.*`
- `Cslib.Logics.LTL.Embedding`
- `Cslib.Logics.LTL.Semantics.GNBA`
- `Cslib.Logics.LTL.Semantics.OmegaRegular`
- `Cslib.Logics.LTL.Semantics.OmegaExecutionSatisfies`

The task description says "update Cslib.lean barrel imports accordingly" — which 4 LTL files to remove is clear, but whether to also remove all Bimodal imports is NOT clear from the description.

### 5. Changing Satisfies.lean to ωSequence Breaks 3 Existing LTL Files on Main

The following files on main use `Satisfies v i φ` (ℕ-indexed API) and will break if Satisfies.lean switches to the ωSequence-based API:

| File | Impact |
|------|--------|
| `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` | Uses `Satisfies v i φ` throughout; defines `omegaLanguage` in terms of it |
| `Cslib/Logics/LTL/Semantics/GNBA.lean` | Uses `Satisfies v i ψ` in canonicalAtom and consistency proofs |
| `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` | Bridges `Satisfies` to `ωSequence` via labeling function |

The feature branch avoids this by removing these files from `Cslib.lean`. On main, these files still exist and would need to be updated or removed.

### 6. ModalConnectives Is Not Mentioned in the Task Description But Is Removed by Feature Branch

This creates a decision fork: does the implementer follow the TASK DESCRIPTION literally (keep `HasBox`/`ModalConnectives`) or follow the FEATURE BRANCH exactly (remove them)? The two are incompatible with keeping main's Bimodal/Modal ecosystem intact.

### 7. Notation Conflict: ◇ and □ Already Defined by Bimodal/Modal

The feature branch introduces `◇` (someFuture) and `□` (allFuture) in the `Cslib.Logic.LTL` namespace. However, on main:
- `Cslib/Logics/Bimodal/Syntax/Formula.lean` defines `□ => Formula.box` and `◇ => Formula.diamond` (scoped to `Cslib.Logic.Bimodal`)
- `Cslib/Logics/Modal/Basic.lean` defines `□ => Proposition.box` and `◇ => Proposition.diamond` (scoped to `Cslib.Logic.Modal`)

Since all are scoped notations, they will coexist without error, but opening both `Cslib.Logic.LTL` and `Cslib.Logic.Bimodal` in the same file will create ambiguity. This is a potential maintenance issue if main keeps both namespaces.

---

## Verification Results

| Claim in Task Description | Verified? | Finding |
|---------------------------|-----------|---------|
| "change untl arg order" | PARTIAL | Both branches have SAME code; only docstrings differ |
| "someFuture from φ U ⊤ to ⊤ U φ" | PARTIAL | Both branches have `.untl .top φ`; only docstring label changes |
| "notation symbols from X/U/𝐅/𝐆 to ◯/𝓤/◇/□" | CONFIRMED | Feature branch uses ◯/𝓤/◇/□; main uses X/U/𝐅/𝐆 |
| "add leadsto (⇝) abbreviation" | CONFIRMED | Feature branch has `Formula.leadsto` and `⇝` notation; main does not |
| "remove HasSince/TemporalConnectives/BimodalConnectives" | CONFIRMED (plus more) | Feature branch removes these AND also removes HasBox/ModalConnectives |
| "remove Burgess references from Connectives.lean" | CONFIRMED | Feature branch removes all Burgess references |
| "rewrite Satisfies.lean to use ωSequence State" | CONFIRMED | Feature branch uses ωSequence + valuation `v : Atom → State → Prop` |
| "update Cslib.lean barrel imports" | AMBIGUOUS | Feature branch removes ~140 lines including non-LTL imports |

---

## Risks and Gaps

### Risk 1 (HIGH): Removing Satisfies' ℕ-indexed API breaks 3 existing files

`OmegaRegular.lean`, `GNBA.lean`, and `OmegaExecutionSatisfies.lean` all use `Satisfies v i φ`. Changing to ωSequence API without updating or removing these files will cause build failures. The implementation must either:
- Remove these 3 files from `Cslib.lean` (matches feature branch scope)
- Update them to use the new API (significant additional work)

### Risk 2 (HIGH): Scope ambiguity in Connectives.lean changes

The task says "remove HasSince/TemporalConnectives/BimodalConnectives" but does NOT say "remove HasBox/ModalConnectives". However, the feature branch removes both. If the implementer only removes what's stated, the result differs from the feature branch's Connectives.lean and may leave an inconsistency (TemporalConnectives gone but HasBox stays, even though they were related through BimodalConnectives).

**Recommendation**: Clarify with the user whether HasBox and ModalConnectives should also be removed. If yes, Logics/Bimodal and Logics/Modal files must be removed from Cslib.lean (or updated to use atomic classes).

### Risk 3 (MEDIUM): Files directly using `HasSince` will break if it's removed

Removing `HasSince` from Connectives.lean will break:
- `Cslib/Foundations/Logic/Axioms.lean` (BX1', BX2H, BX3', etc.)
- `Cslib/Foundations/Logic/ProofSystem.lean` (TemporalBXHilbert, BimodalTMHilbert)
- `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean`

These are NOT LTL files. If the task scope is "LTL only", these files should NOT be changed. `HasSince` may need to stay, OR these files need to be removed from Cslib.lean (as the feature branch did).

### Risk 4 (MEDIUM): ◇ and □ notation conflicts with Bimodal/Modal if both stay on main

If LTL Formula adopts ◇ and □ while Bimodal and Modal stay on main, any file opening both `Cslib.Logic.LTL` and `Cslib.Logic.Bimodal` will have ambiguous notation.

### Risk 5 (LOW): The untl constructor docstring comment in main says "Burgess: event U guard" but code is standard

Implementation needs to update the constructor docstring for `untl` in Formula.lean: `| untl (φ₁ φ₂ : Formula Atom)` — the comment says "Burgess: event U guard" but code semantics treat φ₁ as guard and φ₂ as event. Feature branch corrects this to "guard U event: φ₁ holds until φ₂". This is a pure docstring fix, not a semantic change.

### Risk 6 (LOW): OmegaRegular.lean uses both Burgess label AND correct code

`OmegaRegular.lean` line 341-368: The comments say "guard `φ`, event `ψ`" — this is correct (standard convention). But the variable naming in Satisfies pattern `| .untl ψ φ` has the guard as `ψ` and event as `φ`. Any refactoring that renames the pattern variables could introduce confusion.

---

## Confidence Level

| Finding | Confidence |
|---------|-----------|
| Both branches have `.untl .top φ` for someFuture | HIGH — verified by direct file reads |
| Docstring inconsistency in main (inverted guard/event labels) | HIGH — confirmed against semantics and Axioms.lean |
| Feature branch removes HasBox/ModalConnectives (not stated in task) | HIGH — verified by grep on feature branch Connectives.lean |
| 3 LTL files will break if Satisfies changes to ωSequence | HIGH — verified by reading their Satisfies API usage |
| ◇/□ notation conflicts | HIGH — verified grep on scoped notation declarations |
| Cslib.lean diff is much larger than just LTL imports | HIGH — verified by git diff |
| Task description's "arg order change" is docstring-only | HIGH — both branches have identical `.untl .top φ` in code |
