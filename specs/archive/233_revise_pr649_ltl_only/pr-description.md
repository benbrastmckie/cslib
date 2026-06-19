# PR #649 — Updated Title and Description

## Title

`feat(Logics/LTL): LTL formula type and semantics over omega-words`

---

## Body

This PR adds Linear Temporal Logic (LTL) to CSLib, addressing reviewer feedback from
[pullrequestreview-4528240645](https://github.com/leanprover/cslib/pull/649#pullrequestreview-4528240645).

The original PR included both `LTL` and `Temporal` (bidirectional, past+future). Per reviewer
request, this PR contains **LTL only**. The `Temporal` formula type (with since/past operators)
is deferred to a follow-up PR.

### Files Changed

**`Cslib/Foundations/Logic/Connectives.lean`** (modified)

Adds the LTL-relevant typeclass hierarchy on top of `PropositionalConnectives`:

```
PropositionalConnectives
      (HasBot + HasImp)
               |
   FutureTemporalConnectives
       (+ HasUntil)
               |
        LTLConnectives
         (+ HasNext)
```

New classes: `HasUntil`, `HasNext`, `FutureTemporalConnectives`, `LTLConnectives`.

`HasSince` and `TemporalConnectives` are not included here (deferred to the Temporal PR).

**`Cslib/Logics/LTL/Syntax/Formula.lean`** (new file)

Defines the LTL formula inductive type with primitives `{atom, bot, imp, next, untl}`:

- `Formula.someFuture` (◇): `φ U ⊤` — φ holds at some future point
- `Formula.allFuture` (□): `¬◇¬φ` — φ holds at all future points
- `Formula.leadsto` (⇝): `□(p → ◇q)` — every p-state is eventually followed by a q-state

Notation uses standard LTL unicode symbols per reviewer request:

| Operator | Notation | Unicode | VSCode name |
|----------|----------|---------|-------------|
| next | `◯` | U+25EF | `\bigcirc` |
| until | `𝓤` | U+1D4E4 | `\MCU` |
| eventually | `◇` | U+25C7 | `\Diamond` |
| globally | `□` | U+25A1 | `\Box` |
| leads-to | `⇝` | U+21DD | `\leadsto` |

Note: `□` is scoped to `Cslib.Logic.LTL`; within that scope it means "globally". The modal
`□` (box/necessity) is scoped to the modal logic namespace and does not conflict.

`LTLConnectives` instance registered so `Formula` can be used polymorphically in axiom schemas.

**`Cslib/Logics/LTL/Semantics/Satisfies.lean`** (new file)

Defines LTL satisfaction over omega-words:

```lean
def Satisfies (v : ℕ → (Atom → Prop)) (i : ℕ) : Formula Atom → Prop
  | .atom p => v i p
  | .bot => False
  | .imp φ ψ => Satisfies v i φ → Satisfies v i ψ
  | .next φ => Satisfies v (i + 1) φ
  | .untl φ ψ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```

Uses Burgess convention for `until`: `φ U ψ` holds at `i` when φ holds at some future `j ≥ i`
(the event) and ψ holds at all intermediate points (the guard).

Also defines `Valid` (holds at all time points) and `Satisfiable` (holds at some time point in
some omega-word). Connection to `OmegaExecution` from the LTS library is deferred to future work.

**`references.bib`** (modified)

Adds LTL-relevant references:
- `Kamp1968` — historical foundation (tense logic)
- `Pnueli1977` — seminal LTL paper
- `Burgess1982I` / `Burgess1984` — convention for until (event U guard)
- `VardiWolper1986` — automata-theoretic approach

Removes `GPSS1980` (fairness and past-time operators; belongs in the Temporal PR).

**`Cslib.lean`** (modified)

Adds `Cslib.Logics.LTL.Syntax.Formula` and `Cslib.Logics.LTL.Semantics.Satisfies`.

---

## AI Disclosure

This PR was revised with assistance from Claude (Anthropic). Specifically:
- The notation changes (`◯`, `𝓤`, `◇`, `□`, `⇝`) were implemented by Claude
- The `leadsto` abbreviation and notation were added by Claude
- The `Satisfies.lean` file was adapted from main branch content with Claude assistance
- All generated code was reviewed and verified to build cleanly

This follows the Mathlib AI usage policy.
