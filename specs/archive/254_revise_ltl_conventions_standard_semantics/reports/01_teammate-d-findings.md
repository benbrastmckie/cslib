# Teammate D (Horizons) Findings — Task 254

**Role**: Long-term alignment and strategic direction

---

## Key Findings

### 1. The feature branch made a targeted, well-scoped decision

The branch `feat/temporal-formula-propositional` (commit 3e147123) removed exactly three
bundled typeclass wrappers from `Connectives.lean`:
- `HasBox` and `ModalConnectives`
- `HasSince` and `TemporalConnectives`
- `BimodalConnectives` (with its bridge instance)

What it kept: `HasBot`, `HasImp`, `HasUntil`, `HasNext`, `PropositionalConnectives`,
`FutureTemporalConnectives`, `LTLConnectives`.

The docstring of the feature-branch `Connectives.lean` was explicitly renamed from "Composable
Logics" to "Propositional and Temporal Logic", signaling that the module now scopes only to
LTL-relevant infrastructure.

### 2. Main has extensive non-LTL infrastructure that *actively uses* the removed classes

Files on main that depend on `HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`,
or `BimodalConnectives`:

| File | What it uses |
|------|-------------|
| `Cslib/Foundations/Logic/ProofSystem.lean` | `HasBox` (Necessitation, 14 ModalHilbert classes), `HasSince` (TemporalBXHilbert, BimodalTMHilbert) |
| `Cslib/Foundations/Logic/Axioms.lean` | `HasBox` (modal axioms section), `HasSince` (temporal axiom section) |
| `Cslib/Foundations/Logic/Theorems/Modal/Basic.lean` | `HasBox` as section variable |
| `Cslib/Foundations/Logic/Theorems/Modal/S5.lean` | `HasBox` as section variable |
| `Cslib/Foundations/Logic/Theorems/Temporal/TemporalDerived.lean` | `HasSince` as section variable |
| `Cslib/Logics/Modal/Basic.lean` | `ModalConnectives` instance registration |
| `Cslib/Logics/Temporal/Syntax/Formula.lean` | `TemporalConnectives` instance registration |
| `Cslib/Logics/Bimodal/Syntax/Formula.lean` | `BimodalConnectives` instance registration |

The Modal logic module alone has 14 distinct bundled proof system classes (K, T, D, S4, S5, B,
K4, K5, K45, TB, KB5, D4, D5, DB) all parameterized by `[HasBox F]`. The Temporal module has
`TemporalBXHilbert` and the Bimodal module has `BimodalTMHilbert`, both depending on `HasSince`.

### 3. The convention change is specifically about argument order and notation in the LTL files

The most semantically significant change in the feature branch is a reversal of the `untl`
argument convention:

| Version | `untl φ ψ` means | `someFuture φ` |
|---------|-----------------|----------------|
| **Main** (Burgess) | φ = event, ψ = guard; `someFuture φ = φ U ⊤` | `.untl .top φ` (event first) |
| **Feature branch** (Standard) | φ = guard, ψ = event; `someFuture φ = ⊤ U φ` | `.untl .top φ` (guard first = standard LTL) |

Confusingly, both branches write `someFuture φ = .untl .top φ` but they mean different things:
- On main (Burgess): `.untl .top φ` = `⊤ U φ` ... wait, no — on main `someFuture φ = .untl .top
  φ` where `untl event guard`, so this is `event=⊤, guard=φ` — semantically `⊤ U φ` in standard
  notation. But the docstring says `φ U ⊤`.
- This is the source of the confusion: the Burgess convention reverses what "first" and "second"
  argument mean relative to standard LTL.

The feature branch unifies to the standard convention where `untl φ ψ` = `φ U ψ` with φ first
being the guard (holds throughout) and ψ second being the event (eventually holds).

The semantic content of `someFuture` is identical in both: there exists a future time where the
formula holds. But the `Satisfies.lean` semantics change is deeper — the feature branch changes
the representation from `ℕ → (Atom → Prop)` with index `i` to `ωSequence State` with structural
`head`/`tail` operations, which is architecturally aligned with the `OmegaSequence` infrastructure.

### 4. Notation symbols also changed in the LTL-specific files

| Operator | Main notation | Feature branch notation |
|----------|--------------|------------------------|
| Until | `U` (plain letter) | `𝓤` (mathematical U) |
| Next | `X` (plain letter) | `◯` (circle) |
| Eventually | `𝐅` (bold F) | `◇` (diamond) |
| Globally | `𝐆` (bold G) | `□` (square box) |

The feature branch adopts the standard modal-logic-style symbols (diamond/box) for LTL derived
operators. This creates a potential conflict with `Modal/Basic.lean` which uses `□` for the
box modality and `◇` for diamond — but these are in different scopes (`Cslib.Logic.LTL` vs
`Cslib.Logic.Modal`), so scoping prevents collision in practice.

### 5. The Temporal logic (non-LTL) module uses Burgess convention internally but the direction is standard

`Cslib/Logics/Temporal/Satisfies.lean` on main documents the Burgess convention where
`untl φ ψ` = φ is event, ψ is guard, and `someFuture φ = .untl .top φ` = event φ with trivial
guard ⊤. The semantics clause is:
```lean
| .untl ψ φ => ∃ s, t < s ∧ Satisfies M s φ ∧ ∀ r ...
```
where the pattern `ψ φ` matches constructor order, so φ (second arg = guard in Burgess) is
the event at s. This is internally consistent with the Burgess convention but opposite to the
standard LTL convention used in the feature branch.

---

## Strategic Recommendations

### Recommendation 1: Strictly limit scope to LTL-only files

The task description correctly identifies four specific files to modify:
1. `Cslib/Logics/LTL/Syntax/Formula.lean` — notation + argument order + `leadsto`
2. `Cslib/Foundations/Logic/Connectives.lean` — ONLY the removal of non-LTL classes
3. `Cslib/Logics/LTL/Semantics/Satisfies.lean` — ωSequence-based rewrite
4. `Cslib/Lean` barrel imports

**The task must NOT touch**:
- `Cslib/Logics/Temporal/` — has its own Burgess-convention-based full proof system
- `Cslib/Logics/Modal/` — entire proven-in-CSLib hierarchy depends on `HasBox`
- `Cslib/Logics/Bimodal/` — BimodalConnectives instance is load-bearing
- `Cslib/Foundations/Logic/ProofSystem.lean` — HasBox/HasSince are structurally fundamental
- `Cslib/Foundations/Logic/Axioms.lean` — modal and temporal axiom sections use HasBox/HasSince
- `Cslib/Foundations/Logic/Theorems/Modal/` — uses HasBox throughout

### Recommendation 2: Restore the removed classes from main into the updated Connectives.lean

The task description says to "remove HasSince/TemporalConnectives/BimodalConnectives". However,
these are used by the full `Cslib/Logics/Temporal/`, `Cslib/Logics/Bimodal/`, `Cslib/Foundations/Logic/ProofSystem.lean`,
`Cslib/Foundations/Logic/Axioms.lean`, and `Cslib/Foundations/Logic/Theorems/` modules.

**If these classes are removed**, all 14 `ModalHilbert` subclasses will break (they require
`HasBox`), the `TemporalBXHilbert` and `BimodalTMHilbert` proof system classes will fail
(require `HasSince`), and the `Temporal.Formula` instance registration will fail
(`TemporalConnectives` instance).

The correct approach that respects both the LTL-PR change AND the rest of main is:
- Keep `HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`
  in `Connectives.lean` on main
- Add the NEW classes `FutureTemporalConnectives`, `LTLConnectives` alongside them
- The feature branch's removal of the older classes was valid for a branch that ONLY had LTL
  files, but porting that removal to main where Modal/Temporal/Bimodal exist would break them

Alternatively, if the intent is to eventually phase out those bundled classes in favor of atomic
`HasBox`, `HasSince` usage (which ProofSystem.lean already uses atomically), then this is a
separate larger refactor task that should not be conflated with task 254.

### Recommendation 3: Preserve the Burgess convention in non-LTL modules

The full `Cslib/Logics/Temporal/` module uses the Burgess convention throughout including its
proof system, semantics, and metalogic. Changing `untl` argument order in `Temporal/Syntax/Formula.lean`
would ripple into `Temporal/Semantics/Satisfies.lean`, all axioms, and the 200+ proven results in
the Temporal metalogic. This is a multi-hundred-file change outside task 254's scope.

The LTL module can safely use the standard convention since it is isolated in `Cslib/Logics/LTL/`
and does not inherit from the Temporal module.

---

## Scoping Advice

### What Task 254 SHOULD change (minimal correct scope)

1. **`Cslib/Logics/LTL/Syntax/Formula.lean`** — Full update as described:
   - Argument order convention: `untl` first arg = guard, second = event
   - `someFuture φ = ⊤ U φ` (standard, not Burgess)
   - Notation: `U → 𝓤`, `X → ◯`, `𝐅 → ◇`, `𝐆 → □`
   - Add `leadsto` abbreviation and `⇝` notation
   - Remove Burgess references in docstrings

2. **`Cslib/Logics/LTL/Semantics/Satisfies.lean`** — Full update as described:
   - Switch to `ωSequence State` with `v : Atom → State → Prop`
   - Use `w.head`, `w.tail`, `w.drop j` instead of `v i`, `v (i+1)`, etc.
   - Update argument order in `untl` match arm to standard convention

3. **`Cslib/Foundations/Logic/Connectives.lean`** — Additive update only:
   - ADD `FutureTemporalConnectives` and `LTLConnectives` classes (they are new)
   - KEEP `HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`
   - The docstring can be updated to mention LTL explicitly, but the module must remain
     "Composable Logics" since it serves the full hierarchy

### What Task 254 should NOT change

- `Cslib/Logics/Temporal/` — entirely separate logic with its own conventions
- `Cslib/Logics/Modal/` — entirely separate logic
- `Cslib/Logics/Bimodal/` — entirely separate logic
- `Cslib/Foundations/Logic/ProofSystem.lean` — load-bearing HasBox/HasSince constraints
- `Cslib/Foundations/Logic/Axioms.lean` — modal + temporal axiom sections
- `Cslib/Foundations/Logic/Theorems/Modal/` and `Theorems/Temporal/`

### Risk of over-scoping

If an implementer naively imports the feature branch's `Connectives.lean` verbatim (which removes
`HasBox`, `HasSince`, `ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`), the
following modules will fail to compile:
- All 14 `ModalHilbert` class variants in `ProofSystem.lean`
- `TemporalBXHilbert` and `BimodalTMHilbert`
- `Necessitation` inference rule
- All of `Theorems/Modal/Basic.lean`, `Theorems/Modal/S5.lean`
- `Theorems/Temporal/TemporalDerived.lean`
- `Logics/Modal/Basic.lean` instance registration
- `Logics/Temporal/Syntax/Formula.lean` instance registration
- `Logics/Bimodal/Syntax/Formula.lean` instance registration

This is a breaking change to the full CSLib build. The implementer MUST handle this by being
additive in `Connectives.lean` rather than subtractive.

---

## Confidence Level

**High confidence** on the factual analysis. All claims are grounded in file reads and git diffs.

**High confidence** that the removal of `HasBox`/`HasSince`/`ModalConnectives`/`TemporalConnectives`/`BimodalConnectives` from `Connectives.lean` on main would break the build. This is directly observable from grep results showing 14 `ModalHilbert` classes and 2 temporal/bimodal Hilbert classes all depending on these typeclasses.

**High confidence** that the LTL-only changes (Formula.lean, Satisfies.lean) are safe and self-contained.

**Medium confidence** on the interpretation of the `someFuture` argument order between the two conventions — the Lean code requires careful reading because both versions write `.untl .top φ` but mean opposite things by which argument is event vs guard.

**Recommendation strength**: Strong. The scoping advice in this report directly averts a build-breaking mistake that would require reverting substantial changes to non-LTL modules.
