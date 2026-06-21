# Teammate A Findings: LTL Convention Diff Analysis

**Task**: Revise LTL conventions on main to conform to standard semantic definitions from
`feat/temporal-formula-propositional` (commit `3e147123`).

**Scope**: LTL-specific changes only. The feature branch additionally removed Bimodal, Modal,
and Temporal logic content from Cslib.lean and Connectives.lean; those removals are out of scope
for this task because they would break unrelated formalization on main.

---

## Key Findings

1. **Argument-order mismatch (Formula.lean)**: Main documents `untl` with "Burgess: event U guard"
   (first=event, second=guard), but the feature branch adopts the standard convention (first=guard,
   second=event). Critically, main's actual _semantics_ (Satisfies.lean line 52) already treat
   the first arg as guard and second as event, so main's documentation is internally inconsistent.

2. **Notation change (Formula.lean)**: Main uses ASCII-style bold symbols (`U`, `X`, `𝐅`, `𝐆`).
   Feature branch replaces these with Unicode math symbols (`𝓤`, `◯`, `◇`, `□`) and adds a new
   leads-to operator (`⇝`).

3. **Semantics model change (Satisfies.lean)**: Feature branch replaces the flat `ℕ`-indexed
   model `v : ℕ → (Atom → Prop)` with an `ωSequence`-based model
   `v : Atom → State → Prop, w : ωSequence State`. This is a breaking type-signature change that
   requires rewriting all downstream files that call `Satisfies`.

4. **someFuture swap**: Both branches use `.untl .top φ` for `someFuture`. Under the standard
   convention (first=guard), this correctly reads "⊤ U φ" (⊤ is the trivial guard, φ is the
   event). Under main's claimed Burgess convention (first=event) it would mean ⊤ is the event,
   which contradicts the docstring "F φ := φ U ⊤" — this is the documented inconsistency.

5. **Connectives.lean**: Feature branch removed `HasBox`, `HasSince`, `ModalConnectives`,
   `TemporalConnectives`, `BimodalConnectives`. These cannot be removed on main without breaking
   a large body of Bimodal/Temporal/Modal formalization. The only Connectives.lean changes
   needed are cosmetic (docstring + reference list updates).

6. **Cslib.lean**: No changes required. Main already imports all LTL files. Feature branch
   stripped non-LTL content because it is a focused feature branch; that scope is out of range.

---

## File-by-File Change List

### `Cslib/Logics/LTL/Syntax/Formula.lean`

#### Module header (`/-! # LTL Formula Type`)
- **Remove**: "following the Burgess convention" from the `next`/`untl` separation rationale.
- **Update** `Formula.someFuture` description: `𝐅` → `◇`, "`φ U ⊤`" → "`⊤ U φ`", drop "Burgess".
- **Update** `Formula.allFuture` description: `𝐆` → `□`.
- **Add** `Formula.leadsto (⇝)` to Main definitions section.
- **Rewrite** Notation section: replace `U`/`X`/`𝐅`/`𝐆` with `𝓤`/`◯`/`◇`/`□`, add `⇝`.
- **Rewrite** Derived Operators section: change "Burgess convention: event U guard, first
  argument is the event" → "guard U event: first argument φ₁ is the guard (holds at all
  intermediate points) and the second ψ is the event (eventually holds at the witness point)".
- **Remove** Burgess references from the References section (`[Burgess1982I]`, `[Burgess1984]`).

#### Inductive constructor docstring
- Line `| untl (φ₁ φ₂ : Formula Atom)`:  
  Change comment from `(Burgess: event U guard)` to `(guard U event: φ₁ holds until φ₂)`.

#### `Formula.someFuture` docstring
- Change from: `F φ := φ U ⊤. Uses Burgess convention: φ is the event (holds at witness), ⊤ is the trivial guard.`
- Change to: `◇φ := ⊤ U φ. ⊤ is the trivial guard, φ is the event that eventually holds.`

#### `Formula.allFuture` docstring
- Change `G φ := ¬F ¬φ` to `□φ := ¬◇¬φ`.

#### New definition (add after `allFuture`)
```lean
/-- Leads-to: p ⇝ q := □(p → ◇q). A liveness property asserting that
    every state satisfying p is eventually followed by a state satisfying q. -/
abbrev Formula.leadsto (p q : Formula Atom) : Formula Atom :=
  .allFuture (.imp p (.someFuture q))
```

#### Notation block
Replace:
```lean
@[inherit_doc] scoped infix:40 " U " => Formula.untl
@[inherit_doc] scoped prefix:40 "X" => Formula.next
@[inherit_doc] scoped prefix:40 "𝐅" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "𝐆" => Formula.allFuture
```
With:
```lean
@[inherit_doc] scoped infix:40 " 𝓤 " => Formula.untl
@[inherit_doc] scoped prefix:40 "◯" => Formula.next
@[inherit_doc] scoped prefix:40 "◇" => Formula.someFuture
@[inherit_doc] scoped prefix:40 "□" => Formula.allFuture
@[inherit_doc] scoped infix:20 " ⇝ " => Formula.leadsto
```

#### References section
- Remove: `[Burgess1982I]` and `[Burgess1984]` bib keys.
- Keep: `[Pnueli1977]`, `[Kamp1968]`, `[VardiWolper1986]`.

---

### `Cslib/Logics/LTL/Semantics/Satisfies.lean`

This file undergoes a **complete structural rewrite**.

#### Import change
- Add: `public import Cslib.Foundations.Data.OmegaSequence.Init`
- Remove: (no imports removed; existing import `Cslib.Logics.LTL.Syntax.Formula` kept)

#### Module header update
- Replace flat-valuation description with ωSequence description matching feature branch:
  - Old: "omega-word is represented as a valuation `v : ℕ → (Atom → Prop)`, assigning to each
    time point `i : ℕ` the set of atoms that hold at that point."
  - New: "A `State` type is equipped with a valuation `v : Atom → State → Prop` that determines
    which atomic propositions hold at each state. An omega-word is an `ωSequence State`."
- Update Main definitions:
  - Old: `Satisfies v i φ`, `Valid v φ`, `Satisfiable φ` (time-indexed)
  - New: `Satisfies v w φ` (ωSequence-indexed), `Valid v φ` (over all ωSequences), `Satisfiable φ`
- Remove Burgess language from the `untl` explanation.

#### Variable block change
Old:
```lean
variable {Atom : Type*}
```
New:
```lean
variable {Atom State : Type*}
```

#### `Satisfies` definition rewrite
Old:
```lean
def Satisfies (v : ℕ → (Atom → Prop)) (i : ℕ) : Formula Atom → Prop
  | .atom p => v i p
  | .bot => False
  | .imp φ ψ => Satisfies v i φ → Satisfies v i ψ
  | .next φ => Satisfies v (i + 1) φ
  | .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```
New:
```lean
def Satisfies (v : Atom → State → Prop) (w : ωSequence State) : Formula Atom → Prop
  | .atom p => v p w.head
  | .bot => False
  | .imp φ ψ => Satisfies v w φ → Satisfies v w ψ
  | .next φ => Satisfies v w.tail φ
  | .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ
```

**Important**: The `untl` case semantics change:
- Old (main): `∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ`
  (ψ=first arg=guard, φ=second arg=event; reflexive "j ≥ i")
- New (feature): `∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ`
  (φ=first arg=guard, ψ=second arg=event; strict "k < j" without explicit "j ≥ 0" — trivially
  holds since j : ℕ)

Note: The new definition uses `w.drop j` to shift the sequence rather than directly indexing.

#### `Valid` definition rewrite
Old:
```lean
def Valid (v : ℕ → (Atom → Prop)) (φ : Formula Atom) : Prop :=
  ∀ i, Satisfies v i φ
```
New:
```lean
def Valid (v : Atom → State → Prop) (φ : Formula Atom) : Prop :=
  ∀ (w : ωSequence State), Satisfies v w φ
```

#### `Satisfiable` definition rewrite
Old:
```lean
def Satisfiable (φ : Formula Atom) : Prop :=
  ∃ (v : ℕ → (Atom → Prop)) (i : ℕ), Satisfies v i φ
```
New:
```lean
def Satisfiable (φ : Formula Atom) : Prop :=
  ∃ (v : Atom → State → Prop) (w : ωSequence State), Satisfies v w φ
```

---

### `Cslib/Foundations/Logic/Connectives.lean`

Only **cosmetic/docstring** changes. The modal/temporal/bimodal classes (`HasBox`, `HasSince`,
`ModalConnectives`, `TemporalConnectives`, `BimodalConnectives`) must be **retained** on main to
avoid breaking existing Bimodal/Temporal/Modal formalization.

Specific updates:
- Module doc title: "Composable Logics" → "Propositional and Temporal Logic"
- Module doc summary: streamline to match feature branch tone
- Remove `HasBox`/`HasSince` from the atomic class bullet list (update the design bullet)
- Remove removed bundled classes from the bundled class list description
- Remove reference: `[Heyting1930]`, `[ChagrovZakharyaschev1997]`
- Add reference: `[Avigad2022]` (already in references.bib)
- Drop "Biconditional (`iff`) is deferred to task 173" note

---

### `Cslib/Logics/LTL/Embedding.lean`

Documentation-only changes (the Lean code remains correct, but docstrings reference the old
Burgess-based model):

- Module docstring line: "LTL.Satisfies uses reflexive (non-strict) until: `∃ j ≥ i, ...`"
  Update to reference the new ωSequence model.
- Function docstring for `Formula.toTemporal`: same update.
- Note: The argument-order in `| .untl ψ φ => (toTemporal φ).reflexiveUntl (toTemporal ψ)` is
  preserved. Under both conventions the first-arg is guard and second is event; the Temporal
  `reflexiveUntl φ ψ` puts φ=event first so the mapping `reflexiveUntl(event)(guard)` stays
  correct. Only the label comments need updating.

---

### `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean`

**Major rewrite required** due to Satisfies signature change.

Current structure: `SatisfiesExec labeling ss i φ = Satisfies (fun n => labeling (ss n)) i φ`
using the old flat `v : ℕ → (Atom → Prop)` model.

After the Satisfies rewrite, this bridge definition needs to adapt:
- The new `Satisfies (v : Atom → State → Prop) (w : ωSequence State)` naturally takes an
  `ωSequence State` directly, so the `labeling : State → (Atom → Prop)` bridge may simplify.
- New `SatisfiesExec` can become:
  `SatisfiesExec labeling ss φ = Satisfies (fun p s => labeling s p) ss φ`
  or it may be unnecessary if the caller constructs `v` directly.
- All `satisfiesExec_*` lemmas need updating to remove the `i : ℕ` argument and use ωSequence
  operations (`.head`, `.tail`, `.drop`).
- The theorem `satisfiesExec_untl` docstring reference to "Burgess convention" must be removed.

---

### `Cslib/Logics/LTL/Semantics/OmegaRegular.lean`

**Major rewrite required** (404 lines; 22 Satisfies references).

Key affected areas:
- `Formula.omegaLanguage`: currently `{ v | Satisfies (fun n p => p ∈ v n) 0 φ }`.
  After change: needs to wrap `v : ωSequence (Set Atom)` as an `ωSequence State` and use the
  new Satisfies signature.
- `satisfies_shift`: the private lemma `Satisfies v (i + k) φ ↔ Satisfies (fun n => v (n + k)) i φ`
  is meaningless in the new ωSequence model; the equivalent is `w.drop k ∈ φ.omegaLanguage`.
  The existing `mem_omegaLanguage_drop` theorem (already present as a private lemma) may subsume it.
- All case lemmas (`satisfies_atom`, `satisfies_next`, etc.) need new signatures.
- The `untl` comment "Note: Burgess convention: untl ψ φ means ψ is the guard, φ is the event"
  at line 174 must be removed or updated.

---

### `Cslib/Logics/LTL/Semantics/GNBA.lean`

**Major rewrite required** (1423 lines; 41 Satisfies references).

Key affected areas:
- `Formula.canonicalAtom`: currently `{ ψ ∈ Formula.closure φ | Satisfies v i ψ }` with
  `v : ℕ → (Atom → Prop)` and `i : ℕ`. Must adapt to new Satisfies.
- `Formula.canonicalAtom_isAtom` and all subsequent lemmas using it: need new signatures.
- All inline `Satisfies v i ψ` and `Satisfies (fun n p => p ∈ v n) i ψ` uses: update.
- The IsAtom consistency conditions reference `Satisfies v i`; update throughout.
- The `v' : ℕ → (Atom → Prop)` variable (defined as `fun n p => p ∈ v n`) used internally
  throughout the file needs replacement.
- The argument order note in the untl case (line 174 OmegaRegular.lean) and throughout GNBA
  that says "Burgess convention: untl ψ φ means ψ is the guard, φ is the event" must be removed.

---

## Downstream Dependencies

Files that **must change** (ordered by dependency):

| Priority | File | Change Type | Reason |
|----------|------|-------------|--------|
| 1 | `Cslib/Logics/LTL/Syntax/Formula.lean` | Notation + docstring | Source of convention |
| 2 | `Cslib/Logics/LTL/Semantics/Satisfies.lean` | Complete rewrite | Signature change |
| 3 | `Cslib/Logics/LTL/Semantics/OmegaExecutionSatisfies.lean` | Major rewrite | Downstream of Satisfies |
| 4 | `Cslib/Logics/LTL/Semantics/OmegaRegular.lean` | Major rewrite | Downstream of Satisfies |
| 5 | `Cslib/Logics/LTL/Semantics/GNBA.lean` | Major rewrite | Downstream of Satisfies |
| 6 | `Cslib/Logics/LTL/Embedding.lean` | Docstring update | References old model |
| 7 | `Cslib/Foundations/Logic/Connectives.lean` | Docstring/reference update | Cosmetic only |

Files that **do NOT need to change**:
- `Cslib.lean` — already imports all LTL files; no LTL-specific additions needed on main
- All Bimodal, Temporal, Modal, Propositional files — do not use LTL.Satisfies
- `references.bib` — `Avigad2022`, `Burgess1982I`, `Burgess1984` already present

Files with **no LTL.Satisfies usage outside LTL directory**: confirmed by grep, zero results.

---

## Key Semantic Question for Implementation

The feature branch `Satisfies.lean` uses a stricter `untl` case:
```lean
| .untl φ ψ => ∃ j, Satisfies v (w.drop j) ψ ∧ ∀ k < j, Satisfies v (w.drop k) φ
```
Here `j : ℕ` is unbounded (not required to be strictly positive). This means `j = 0` is
allowed: `w.drop 0 = w`, so `ψ` can hold immediately. This is the **reflexive** until: φ U ψ
holds at w if ψ holds now (j=0) or at some future position j > 0 with φ holding at all k < j.

The main branch `Satisfies.lean` has the same semantics written differently:
```lean
| .untl ψ φ => ∃ j ≥ i, Satisfies v j φ ∧ ∀ k, i ≤ k → k < j → Satisfies v k ψ
```
where `j ≥ i` and `i ≤ k → k < j` — reflexive since j = i is allowed.

Both are reflexive until. The GNBA.lean will need careful auditing to ensure the canonicalAtom
construction remains sound under the ωSequence model.

---

## Confidence Level

- **Formula.lean change list**: High confidence. Diff is clear and mechanical.
- **Satisfies.lean rewrite**: High confidence. Feature branch version is authoritative and clean.
- **Connectives.lean scope**: High confidence. Modal/bimodal classes must be retained on main.
- **Downstream file impact assessment**: High confidence on which files are affected; medium
  confidence on exact proof repair needed for GNBA.lean (complex 1423-line file).
- **Cslib.lean**: High confidence — no change needed.
- **Embedding.lean argument-order safety**: High confidence — existing code remains semantically
  correct; only docstrings need updating.
- **OmegaExecutionSatisfies.lean rewrite scope**: Medium confidence — the bridge definition
  may simplify significantly under the new Satisfies, but exact shape requires implementation.
