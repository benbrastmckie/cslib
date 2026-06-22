# Research Report: LTL vs Temporal Convention Documentation

## Task

Add module-level documentation contrasting the LTL and Temporal convention differences across three files:
1. `Cslib/Logics/LTL/Syntax/Formula.lean` -- add a note about convention differences
2. `Cslib/Logics/Temporal/Syntax/Formula.lean` -- add a cross-reference to LTL convention
3. `Cslib/Foundations/Logic/Connectives.lean` -- note which typeclasses serve which modules

## Current Documentation State

### LTL/Syntax/Formula.lean (lines 13-57)

**Already documents:**
- "Derived Operators" section (lines 46-49) explains: `untl phi psi` has phi as **guard** and psi as **event**
- `someFuture phi` is `top U phi` (top is trivial guard, phi is event)
- Notation section lists `U` (infix, 40), `circle` (prefix, 40), `diamond` (prefix, 40), `box` (prefix, 40)

**Missing:**
- No cross-reference to Temporal module or Burgess convention
- No note that LTL follows the "standard" convention while Temporal follows Burgess
- No mention of Embedding.lean as the bridge between the two conventions

### Temporal/Syntax/Formula.lean (lines 13-63)

**Already documents:**
- "Derived Temporal Operators" section (lines 49-57) explicitly states "Burgess convention"
- Explains: in `untl event guard`, first argument is **event**, second is **guard**
- Individual abbrev docstrings mention "Burgess convention" (lines 102-103, 112-113)
- References to "standard LTL" appear in abbrev docstrings (e.g., "Equivalent to standard LTL `F phi = top U phi` semantically")

**Missing:**
- No formal cross-reference to `Cslib.Logics.LTL` module in the module docstring
- No explicit comparison table or note saying "LTL uses standard convention (guard U event) while this module uses Burgess (event U guard)"
- No mention of Embedding.lean as the bridge

### LTL/Embedding.lean (lines 12-33)

**Already documents (task 255 updated this):**
- "LTL uses the standard convention `untl guard event`, while Temporal uses the Burgess convention `untl event guard`"
- "The embedding bridges the two by swapping arguments"
- Explains reflexiveUntl for bridging reflexive/strict until semantics
- References both Pnueli1977 and Burgess1984

**Status:** This file already has excellent documentation. No changes needed here.

### Foundations/Logic/Connectives.lean (lines 11-54, 56-168)

**Already documents:**
- Module docstring mentions "four logic levels (Propositional, Modal, Temporal, Bimodal)"
- Each bundled class has a docstring explaining its role
- `LTLConnectives` docstring (lines 136-141) explains it extends `FutureTemporalConnectives` with `HasNext`
- `TemporalConnectives` docstring (lines 143-147) explains it extends with `HasSince`

**Missing:**
- No note explaining which atomic classes serve which modules
- No mention that `HasSince`/`TemporalConnectives`/`BimodalConnectives` serve Temporal and Bimodal
- No mention that `HasUntil`/`HasNext`/`FutureTemporalConnectives`/`LTLConnectives` serve LTL
- No convention difference note (guard vs event argument order)

## No Barrel File

There is no `LTL.lean` barrel file at the `Cslib/Logics/` level. The LTL module structure is:
```
Cslib/Logics/LTL/
  Embedding.lean
  Semantics/
    GNBA.lean
    OmegaExecutionSatisfies.lean
    OmegaRegular.lean
    Satisfies.lean
  Syntax/
    Formula.lean
```

Creating a barrel file is not needed for this task -- the module docstring in `Formula.lean` is the natural place for the LTL-side documentation, since it is the root syntax file that all other LTL modules import.

## Proposed Changes

### Change 1: LTL/Syntax/Formula.lean module docstring

Add a new section after the existing "Derived Operators" section (before "References") contrasting the convention difference. Insert approximately at line 51 (after the Derived Operators explanation):

```
## Convention Note

LTL follows the **standard** (Pnueli) convention for until: in `untl guard event`, the
first argument is the guard (holds at all intermediate points) and the second is the event
(eventually holds at the witness point). This is the convention used by Pnueli [Pnueli1977],
Vardi-Wolper [VardiWolper1986], and most verification-oriented LTL literature.

The `Cslib.Logic.Temporal` module uses the **Burgess** convention with swapped argument order:
`untl event guard`. The canonical embedding `Formula.toTemporal` in
`Cslib.Logics.LTL.Embedding` bridges the two conventions, mapping LTL's reflexive until
to Temporal's strict `reflexiveUntl`.
```

### Change 2: Temporal/Syntax/Formula.lean module docstring

Add a cross-reference note after the "Derived Temporal Operators" section (before "References"). Insert approximately at line 57:

```
## Convention Note

This module uses the **Burgess** convention: in `untl event guard` and `snce event guard`,
the first argument is the event and the second is the guard. The `Cslib.Logic.LTL` module
uses the **standard** (Pnueli) convention with swapped argument order: `untl guard event`.
See `Cslib.Logics.LTL.Embedding` for the canonical embedding that bridges the two conventions.
```

### Change 3: Foundations/Logic/Connectives.lean module docstring

Add a new section after the "Design" section (before "References") explaining module routing. Insert approximately at line 53:

```
## Module Routing

The bundled connective classes route to specific logic modules:

- `FutureTemporalConnectives` / `LTLConnectives` (`HasUntil`, `HasNext`):
  serve `Cslib.Logics.LTL`, which uses the standard (Pnueli) convention (`untl guard event`).
- `TemporalConnectives` (`HasUntil`, `HasSince`):
  serve `Cslib.Logics.Temporal`, which uses the Burgess convention (`untl event guard`).
- `BimodalConnectives` (`HasUntil`, `HasSince`, `HasBox`):
  serve `Cslib.Logics.Bimodal`, combining temporal and modal connectives.

Note that `HasUntil` is shared: the argument-order convention (guard-first vs event-first)
is determined by the concrete formula type's instance, not by the typeclass itself.
```

## Implementation Complexity

This is a documentation-only task with zero proof obligations. All changes are additions to `/-! ... -/` module docstring blocks. No Lean code is modified, so there is no risk of breaking builds.

**Estimated effort:** 3 edits, each inserting a short text block into an existing docstring.

## Verification

After edits:
- `lake build Cslib.Logics.LTL.Syntax.Formula` to verify no docstring syntax errors
- `lake build Cslib.Logics.Temporal.Syntax.Formula` likewise
- `lake build Cslib.Foundations.Logic.Connectives` likewise
- Or simply `lake build` as a final check
