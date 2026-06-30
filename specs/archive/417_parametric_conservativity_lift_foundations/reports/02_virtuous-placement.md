# Task 417 — Research (Hard): The Most Virtuous Placement for the Parametric Conservativity Lift

**Task type**: cslib (Foundations/Logics architecture — module placement)
**Mode**: `--hard` (H2 anti-analysis, H3 reference grounding, H4 adversarial self-verification)
**Reference grounding tier**: Tier 3 (implementation-backed refactor) with a Tier 1 governing spec
(`ORGANISATION.md`) and one Tier 1 external precedent (`ModelTheory`, Mathlib).
**Status**: researched — no Lean source modified
**Date**: 2026-06-29
**Supersedes the placement verdict of**: `reports/01_conservativity-lift-design.md` §6 (which recommended
Foundations placement + docstring). This report retracts that recommendation.

---

## 0. Verdict (opinionated, single answer)

**THE virtuous placement is Option 2: move the file to**

```
Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean
```

**keeping `namespace Cslib.Logic` and both theorem signatures byte-for-byte unchanged.**

This is not a compromise and not the "fallback" of report 01 — it is the placement that the
dependency DAG's *intended meaning* actually dictates. The current Foundations placement is a
genuine layering inversion that should be removed, not documented. The cited precedent
(`DiegoEmbedding.lean`) is **itself a smell**, not a sanction (§4). Option 3 ("abstract interface
in Foundations, parametric over any classical propositional base") is **abstraction for its own
sake** under CSLib's present contents and is rejected with a precise trigger condition for when it
would become correct (§6.3). Option 4 (new layer) is unjustified (§6.4).

Migration cost: **one `git mv`, two consumer import-line edits, one barrel regen, zero signature
changes, zero new cross-layer edges** (it *removes* one) — verified acyclic (§7).

---

## 1. Source-to-Implementation Mapping

| Source claim (governing) | Locus / BibKey | Lean target | Translation note |
|---|---|---|---|
| "Foundations = general-purpose definitions and results shared across specific logics… instantiated by each logic" | `ORGANISATION.md:10,22` | placement invariant: no `Foundations/* → Logics/*` edge | The DAG edge `A→B` means "A built from B's *more primitive* abstraction"; Foundations→Logics asserts the reverse |
| "Each logic instantiates the abstract infrastructure from `Foundations/Logic/`" | `ORGANISATION.md:78` | confirms direction `Logics → Foundations` | The lift is *about* a specific logic (PL), so it is a Logics citizen |
| Dependency hierarchy diagram (PL is the root logic, Modal/Temporal above, Bimodal at the join) | `ORGANISATION.md:82–95` | `Propositional/Metalogic` is the lowest module visible to all three clients | Lowest-common-ancestor placement is in PL, not Foundations |
| "`Cslib.Logic` namespace spans both `Foundations/Logic/` and `Logics/`" | `ORGANISATION.md:254–264` | keep `namespace Cslib.Logic` → name-invariant move | Namespace does not encode file tree; moving the file renames nothing |
| Generic metatheory parameterized over an interface lives *with its subject*, in its own subtree (not hoisted into a lower layer) | Mathlib `ModelTheory.*` (verified via leanfinder) | `Propositional/Metalogic/ConservativityLift.lean` | `ModelTheory` is generic over `Language` yet lives in the model-theory subtree; analogue: generic-over-embedding-target lives in PL's metatheory |
| Classical-scope rationale for the three embeddings | `ORGANISATION.md:213–247`; `ChagrovZakharyaschev1997` (`references.bib`, verified key) | informs that the lift certifies the **CPL** fragment | No theorem-number citation needed; architectural, not proof-transcription |

BibKey verification: `ChagrovZakharyaschev1997` **present** in `references.bib` (verified). No new
BibKey required; this task is architectural and grounds on `ORGANISATION.md` as the in-repo spec.

---

## 2. What the file actually depends on (the load-bearing fact)

Verified import block of the current file (`ConservativityLift.lean:7–14`):

```
public import Cslib.Init
public import Cslib.Logics.Propositional.Semantics.Bool          -- PL.Proposition, PL.Evaluate
public import Cslib.Logics.Propositional.Metalogic.StrongCompleteness -- prop_completeness, PropositionalAxiom, Derivable
```

Both generic theorems are parametric over the **embedding target** `Tgt` and an abstract
`sat : Tgt → Prop`, but their *subject* is the **concrete** CSLib propositional logic:

- `evaluate_iff_of_classicalBridge` recurses by `induction ψ` over `PL.Proposition` and unfolds
  `PL.Evaluate` (verified `ConservativityLift.lean:64–99`). It needs **only** `Semantics/Bool`.
- `conservative_over_cpl` is `apply prop_completeness; …` (verified `:114–116`). It needs
  `Metalogic/StrongCompleteness`.

`PL.Evaluate` (verified `Semantics/Bool.lean:57–62`) and `prop_completeness`
(`Tautology φ → Derivable PropositionalAxiom φ`, verified `StrongCompleteness.lean:34`) are concrete
declarations in `Cslib.Logic.PL`. **The genericity is over the target type; the subject is fixed PL.**
This single fact decides the architecture: the file's true minimal home is the lowest module that
sees `PL.Evaluate` + `prop_completeness`, which is `Logics/Propositional/Metalogic`.

---

## 3. What the dependency DAG is *supposed to mean* (semantic reading)

`ORGANISATION.md` is unambiguous:

- §10: *"`Foundations/` — General-purpose definitions and results shared across specific logics."*
- §22: *"It defines abstract proof systems, connective typeclasses, and generic theorems that are
  **instantiated by each logic**."*
- §78: *"Each logic **instantiates the abstract infrastructure from** `Foundations/Logic/`."*

The intended meaning of an edge `X → Y` (X imports Y) is therefore **"X is built out of Y's
more-primitive, logic-agnostic abstraction."** Foundations is the *floor*: a connective typeclass
(`HasImp`), an abstract `InferenceSystem`, a `GenericMCS` — things with **no commitment to any one
logic's syntax**. `Logics/Propositional` is the *first concrete logic* sitting on that floor.

An edge `Foundations/Logic/Metalogic → Logics/Propositional` asserts "the abstract floor is built
out of a specific logic's completeness theorem." That is **semantically backwards**: it makes the
floor depend on the furniture. It is not a lint nuisance — it inverts the *only* structural
invariant that distinguishes the two directories. The `Cslib.Logic` namespace deliberately spans
both trees (§254–264), so the **namespace gives no cover**: the directory split *is* the layering
contract, and this file currently violates it.

The lift is not logic-agnostic. It mentions `PL.Proposition`, `PL.Evaluate`, `PropositionalAxiom`,
`PL.Derivable` — four concrete PL objects. It is **propositional metatheory that happens to be
generic over embedding targets**. Generic-over-target ≠ logic-agnostic. Its home is PL's metatheory.

---

## 4. The cited precedent is a smell, not a sanction

Report 01 and the file docstring justify the inversion by citing
`Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean:15–16`. I read it and the files it imports.
**It does not sanction the inversion; it is another instance of the same defect.**

- `DiegoEmbedding.lean` (in `Foundations/Order`) imports
  `Logics/Propositional/Semantics/Algebra/{FragmentPredicates,Hilbert}.lean` (verified `:14–16`).
- `Algebra/Hilbert.lean` itself imports **both** `Cslib.Foundations.Order.HilbertAlgebra` **and**
  `Cslib.Logics.Propositional.Defs` (verified header). It is a *Logics-side bridge* gluing PL
  syntax to the Foundations `HilbertAlgebra`.
- So `DiegoEmbedding` — whose theorem is **pure order theory** (every Hilbert algebra embeds into a
  Heyting algebra; Diego 1966 / Rasiowa 1974) — reaches *up* into `Logics/Propositional` to borrow
  PL-algebra evaluation machinery. The order-theoretic result has **no intrinsic need** for
  `PL.Proposition`; the dependency exists only because the PL→algebra `AlgEvaluate`/fragment
  lemmas were placed Logics-side.

**Defect bar (H2) for the precedent claim** — four elements, all met:
1. *Counterexample to "sanctioned precedent":* a Foundations/Order theorem about algebras depends on
   `Logics/Propositional/Semantics/Algebra`, an avoidable upward edge.
2. *Current behavior:* `DiegoEmbedding` (Foundations) imports Logics; report 01 cites this as the
   established exception licensing a *second* Foundations→Logics edge.
3. *Required behavior:* a Foundations file should depend only on logic-agnostic abstractions;
   PL-specific bridges belong Logics-side.
4. *Isolation:* the edge is in `DiegoEmbedding.lean:15–16` and the dual import in
   `Algebra/Hilbert.lean` header — both reachable upward-pointing edges.

**Conclusion:** citing `DiegoEmbedding` to justify task 417's inversion *propagates* a smell. One
inverted edge does not establish a rule; it establishes a second data point for "this directory
boundary is being eroded." The virtuous move removes 417's edge rather than normalizing it (and, as
a side note, flags `DiegoEmbedding` for a future audit — out of scope here, candidate spawn task).

---

## 5. The DAG, verified (acyclicity of the recommendation)

```
Foundations/Logic           (abstract floor: typeclasses, InferenceSystem, GenericMCS)
        │
        ▼
Logics/Propositional/Defs, /Semantics/Bool, /Metalogic/StrongCompleteness   (PL core + metatheory)
        │  ◄── PUT ConservativityLift HERE (Propositional/Metalogic)
        ├─────────────────────┐
        ▼                     ▼
   Logics/Modal         Logics/Temporal      (import PL; import the lift)
        │                     │
        └──────────┬──────────┘
                   ▼
             Logics/Bimodal                  (import PL; import the lift)
```

Verified facts underpinning acyclicity:

- **`Logics/Propositional` imports nothing from `Modal`/`Temporal`/`Bimodal`** — grep over the whole
  `Logics/Propositional/` subtree returns zero such imports. So a file in `Propositional/Metalogic`
  cannot create a cycle with the three clients.
- The lift file imports **only** `Propositional` (`Bool`, `StrongCompleteness`) + `Init` — it does
  **not** import any client (it is parametric over `Tgt`). So it adds **no** edge into Modal/Temporal/
  Bimodal.
- All three clients **already** import `Logics/Propositional` (e.g. Bimodal `PropositionalConservativity.lean:13`
  imports `…Propositional.Metalogic.StrongCompleteness`; Temporal/Modal extend PL by construction).
  Adding `import …Propositional.Metalogic.ConservativityLift` rides an **existing** edge direction.

Therefore Option 2 is acyclic by construction, and it is the **lowest-common-ancestor** placement:
`Propositional/Metalogic` is the deepest module that (a) sees `PL.Evaluate` + `prop_completeness`
and (b) is visible to all three clients. That is the textbook "least-imports" home.

---

## 6. Candidate architectures, adjudicated

### 6.1 Option 1 — accept the inversion as a documented rule (REJECT)

Make "`Foundations.Logic.Metalogic` may depend on the propositional core" a deliberate, documented
rule.

- **For:** zero code motion; the file already builds green; PL completeness *is* shared substrate.
- **Against (decisive):** it dissolves the one invariant that gives `Foundations` vs `Logics` any
  meaning. Once "Foundations may import the propositional core when convenient" is a rule, the floor
  is no longer a floor — every later author has license to reach down into PL (then Modal, then …)
  "because it's shared." The distinction collapses into a naming convention. The substrate argument
  is also **false on the merits**: CPL completeness is *not* logic-agnostic infrastructure — it is a
  theorem about one concrete logic, already correctly located in `Logics/Propositional/Metalogic`.
  Genuinely shared, logic-agnostic substrate already lives in Foundations (`InferenceSystem`,
  `GenericMCS`, `Consistency`); the lift is not of that kind. **Reject.**

### 6.2 Option 2 — `Logics/Propositional/Metalogic/ConservativityLift.lean` (ADOPT)

- **For:** respects the DAG's intended meaning (§3); acyclic and lowest-common-ancestor (§5);
  name-invariant because `namespace Cslib.Logic` spans both trees (§3); removes one inverted edge and
  the need to cite the `DiegoEmbedding` smell; matches the Mathlib `ModelTheory` precedent of keeping
  interface-generic metatheory in its subject's subtree (§1, leanfinder-verified). Trivial cost (§7).
- **Against:** the file's name reads "conservativity" while it physically sits under `Propositional`,
  not under the modal clients — a momentary "why is the bridge in PL?" for a reader. Answer (and it is
  the *right* answer): conservativity *of* L *over* PL is a fact whose generic content is purely
  propositional + an abstract target; PL's metatheory is precisely where "PL relates to its
  embeddings" belongs. This is a feature (it advertises that the result is PL-driven), not a defect.
  **Adopt.**

### 6.3 Option 3 — extract an abstract `ClassicalPropositionalBase` interface into Foundations (REJECT, with trigger)

The aspiration: make the lemma parametric over *any* classical propositional base via a typeclass in
Foundations, so Foundations depends on nothing in Logics and PL is merely one instance. Sketch:

```lean
-- hypothetical, in Foundations/Logic/…
class ClassicalPropositionalBase (Form : Type*) (Atom : outParam Type*) where
  atom  : Atom → Form
  bot   : Form
  imp   : Form → Form → Form
  and   : Form → Form → Form
  or    : Form → Form → Form
  Eval  : (Atom → Prop) → Form → Prop
  Deriv : Form → Prop
  eval_atom : ∀ v p, Eval v (atom p) ↔ v p
  eval_bot  : ∀ v, ¬ Eval v bot
  eval_imp  : ∀ v a b, Eval v (imp a b) ↔ (Eval v a → Eval v b)
  eval_and  : ∀ v a b, Eval v (and a b) ↔ (Eval v a ∧ Eval v b)
  eval_or   : ∀ v a b, Eval v (or a b)  ↔ (Eval v a ∨ Eval v b)
  completeness : ∀ φ, (∀ v, Eval v φ) → Deriv φ
  -- …and, fatally, a recursor:
  rec : ∀ {motive : Form → Sort _}, (∀ p, motive (atom p)) → motive bot →
        (∀ a b, motive a → motive b → motive (imp a b)) → … → ∀ φ, motive φ
  -- + computation rules for rec on each constructor
```

- **Achievable? Only at a high cost.** `evaluate_iff_of_classicalBridge`'s proof is a **structural
  induction over `PL.Proposition`** (`induction ψ with | atom | bot | imp | and | or`). You cannot
  `induction` an abstract `Form`. To recover it you must bundle a recursor *and its five computation
  rules* into the class — i.e., axiomatize that `Form` is the **initial algebra** of the propositional
  signature. At that point the typeclass *is* `PL.Proposition` re-encoded as an algebraic theory, and
  any instance must prove the computation rules. You have reinvented the inductive type.
- **Does it buy reuse? No — one instance.** CSLib has exactly **one** classical propositional base:
  `PL.Proposition` with `PL.Evaluate` and `prop_completeness`. A typeclass with a single instance,
  whose construction reconstructs the very inductive it abstracts, is abstraction for its own sake. It
  adds a layer of indirection, a recursor obligation, and `outParam` friction, and buys nothing today.
- **Mathlib's own standard rejects it.** Mathlib abstracts `ModelTheory` over `Language` because there
  are *unboundedly many* languages; it does **not** wrap a single concrete object in a one-instance
  class. The maxim "generalize when ≥2 genuine instances exist" is violated here.
- **Trigger for when Option 3 becomes correct:** if/when CSLib gains a **second** classical
  propositional base (e.g. a distinct formula type — a sequent-style or De Bruijn PL — with its *own*
  evaluation and completeness) **and** both want the embedding-conservativity lemma, then a shared
  interface earns its keep. Even then, prefer abstracting over `Eval`/`completeness` while keeping the
  concrete inductive for induction (a *mixin* over a fixed syntax), not a full initial-algebra class.
  **Reject now; revisit only on that trigger.**

### 6.4 Option 4 — a new intermediate layer (REJECT)

A new directory (e.g. `Foundations/Logic/Conservativity/` or a `Logics/Shared/`) for "metatheory
above PL but below the modal family." Unjustified: the existing hierarchy *already has* that slot —
it is `Logics/Propositional/Metalogic`, which by the verified DAG sits above PL core and below all
clients. Inventing a layer to host a two-theorem, ~75-line file is over-engineering and creates a new
top-namespace/aggregator surface for no semantic gain. **Reject.**

---

## 7. Migration plan and cost (Option 2)

**Decls that move:** the file in its entirety (`evaluate_iff_of_classicalBridge`,
`conservative_over_cpl`). **No signature changes. No name changes.** `namespace Cslib.Logic` is
retained — verified correct under `ORGANISATION.md:254–264` and placement-independent, so every
reference resolves unchanged (consumers are in `Cslib.Logic.*`; they already see
`Cslib.Logic.evaluate_iff_of_classicalBridge` / `…conservative_over_cpl`).

**Exact steps:**

1. `git mv Cslib/Foundations/Logic/Metalogic/ConservativityLift.lean
   Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean`
2. In the moved file, **delete** the inversion apparatus that is now obsolete:
   - the header comment `ConservativityLift.lean:9–11` ("Foundations → Logics import…")
   - the `## Architecture Note` paragraph (`:32–37`) citing `DiegoEmbedding`.
   (The two `public import Cslib.Logics.Propositional.*` lines stay; they are now *intra-layer*.)
3. Update the **two** wired consumers' import lines
   (`Cslib.Foundations.Logic.Metalogic.ConservativityLift` →
   `Cslib.Logics.Propositional.Metalogic.ConservativityLift`):
   - `Cslib/Logics/Temporal/ConservativeExtension.lean:9`
   - `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/PropositionalConservativity.lean:9`
4. Regenerate the barrel: `lake exe mk_all --module` (rewrites `Cslib.lean:86` from the Foundations
   path to the Propositional path automatically).
5. Verify: `lake build Cslib.Logics.Propositional.Metalogic.ConservativityLift`, then
   `lake build`, `lake exe checkInitImports`, `lake exe lint-style`,
   `lake shake --add-public --keep-implied --keep-prefix`, `lake test`.

**Dependency-edge delta:**
- **Removed:** `Cslib/Foundations/Logic/Metalogic → Cslib/Logics/Propositional` (the inversion).
- **Added:** none cross-layer. The lift's imports become intra-`Logics/Propositional`; the three
  clients' new import rides the already-present `client → Propositional` direction.
- **Net:** the import graph strictly improves (one inverted edge deleted; none added). Acyclic (§5).

**Cost class:** trivial / XS. ~1 file move, ~4 deleted doc lines, 2 import-line edits, 1 barrel
regen, full-CI reverify. No proof edits, no signature edits, **zero** new `sorry`/axiom (the proofs
are untouched). The Modal re-home stays optional exactly as in report 01 (and, if later done, lands
naturally in the same `Propositional/Metalogic` home with no extra layering question).

---

## 8. Zero-debt / reuse check (CSLib protocol)

1. **Foundations first:** searched `Foundations/Logic/Metalogic/` — `GenericMCS`, `Consistency`,
   `DeductionHelpers`, `ListDeduction`, etc.; none host embedding-conservativity, and (per task 419's
   spike `:116`, `:192–196`) none *can* without reinventing the per-logic `DerivationTree` recursor.
   So no existing Foundations abstraction absorbs the lift — confirming it is **not** Foundations-shaped.
2. **Typeclass hierarchy:** `HasImp`/`HasBot`/… (`Foundations/Logic/Axioms.lean`) describe connectives
   abstractly but carry no `Evaluate`/`completeness`; they cannot express the bridge's induction. No
   reuse available; building one (Option 3) is one-instance over-abstraction (§6.3).
3. **Notation:** none introduced; N/A.
4. **Mathlib instantiable version:** none — `PL.Proposition`/`PL.Evaluate`/`prop_completeness` are
   CSLib-specific. Mathlib offers only the *placement precedent* (`ModelTheory` keeps interface-generic
   metatheory in-subtree), which this recommendation follows.
5. **Logics namespace:** the concept already lives across `Temporal/ConservativeExtension`,
   `Bimodal/.../PropositionalConservativity`, and `Modal/Metalogic/ConservativeExtension`; the lift
   consolidates their shared core. Correct home for the consolidation is PL's metatheory, beneath them.

**Zero-debt:** no `sorry`, no axiom, no vacuous def introduced or required. The move is
proof-preserving.

---

## 9. Adversarial Self-Verification (H4)

Challenged each load-bearing claim of my own recommendation:

- **C1 — "Option 2 is more virtuous than Option 1, not just tidier."** *Challenge:* maybe the docstring
  in Option 1 is enough and the move is churn. *Verification:* Option 1 requires *normalizing* a rule
  ("Foundations may import the propositional core") whose generalization erases the Foundations/Logics
  invariant; the cost of Option 2 is ~XS and *removes* the edge instead of legitimizing it. The
  asymmetry (permanent invariant erosion vs. one-time XS move) confirms Option 2. **Upheld.**
- **C2 — "Does my preferred Option 2 actually avoid the cycle?"** *Challenge:* could PL metatheory
  transitively pull in a client? *Verification:* grep proved `Logics/Propositional/*` imports **no**
  Modal/Temporal/Bimodal; the lift imports only `Bool`+`StrongCompleteness`. Acyclic. **Upheld.**
- **C3 (the key adversarial prompt) — "Does the Option-3 interface buy reuse, or is it abstraction for
  its own sake?"** *Verification:* it has **exactly one** possible instance under current CSLib
  contents, and its proof obligation forces re-encoding `PL.Proposition`'s recursor + computation rules
  (initial-algebra axiomatization). That is the textbook signature of abstraction-for-its-own-sake.
  **My recommendation deliberately rejects the option the user's framing leaned toward**, and I give a
  precise, falsifiable trigger (≥2 classical propositional bases) under which it would flip. I did not
  rubber-stamp the "more abstract = more virtuous" instinct. **Rejected on evidence.**
- **C4 — "Is the DiegoEmbedding precedent really a smell, or am I over-reaching to win the argument?"**
  *Verification:* read the file and its imports; the order-theoretic Diego theorem has no intrinsic
  need for `PL.Proposition`, yet imports `Logics/Propositional/Semantics/Algebra`. That is an
  avoidable upward edge → genuinely a smell, met the 4-element defect bar (§4). Claim survives. I
  scoped a `DiegoEmbedding` audit *out* (separate concern) rather than overloading this task. **Upheld,
  scoped.**
- **C5 — "Is `namespace Cslib.Logic` really fine in `Propositional/Metalogic`, or should it be
  `Cslib.Logic.PL`?"** *Verification:* `ORGANISATION.md:254–264` explicitly makes `Cslib.Logic` span
  both trees; the lemmas are generic over the embedding target (not PL-internal), so the *broader*
  `Cslib.Logic` prefix is the more honest namespace **and** keeps the move name-invariant. Choosing
  `Cslib.Logic.PL` would force needless consumer renames for no semantic gain. **Upheld.**
- **C6 — "Does any downstream task (419) force Foundations placement?"** *Verification:* task 419's
  spike (`:116`, `:192–196`) states the lift "cannot be expressed where the task wants it" in
  Foundations anyway and that no Foundations abstraction can host it without the per-logic recursor.
  419 imposes **no** Foundations constraint. **Upheld.**

No claim was revised to a weaker form; one (DiegoEmbedding audit) was explicitly scoped out. No
forbidden analysis-only verdict: this report ends in an executable migration plan (§7). **No
fundamental flaw found; recommendation stands. No `## Revised Direction` needed.**

---

## 10. Memory candidates

1. *(architecture, CSLib)* "A theorem that is *generic over an embedding target* but whose *subject* is
   a concrete logic (uses that logic's syntax/evaluation/completeness) belongs in **that logic's**
   metatheory subtree, not in `Foundations`. Genericity-over-target ≠ logic-agnostic. Lowest-common-
   ancestor placement = the deepest module seeing all concrete dependencies and visible to all clients."
2. *(smell, CSLib)* "`Foundations/Order/HilbertAlgebra/DiegoEmbedding.lean` imports
   `Logics/Propositional/Semantics/Algebra/*` — a Foundations→Logics inversion. It is a smell, not a
   sanctioned precedent; do not cite it to justify further inversions. Candidate audit/refactor."
3. *(principle, Lean/Mathlib)* "Don't wrap a single concrete inductive in a typeclass to gain
   'parametricity': structural-induction proofs force re-encoding the recursor + computation rules
   (initial-algebra axiomatization), and a one-instance class buys no reuse. Abstract only at ≥2
   genuine instances (cf. Mathlib `ModelTheory` over `Language`)."

---

## 11. Definitive recommendation (restated)

- **Module path:** `Cslib/Logics/Propositional/Metalogic/ConservativityLift.lean`.
- **Namespace:** `Cslib.Logic` (unchanged).
- **New abstract interface:** **none** (Option 3's typeclass is rejected as one-instance over-
  abstraction; precise re-evaluation trigger documented).
- **Edges introduced:** none cross-layer; **one inverted edge removed**
  (`Foundations/Logic/Metalogic → Logics/Propositional`). Verified acyclic.
- **Decls that move/change:** `evaluate_iff_of_classicalBridge`, `conservative_over_cpl` move verbatim;
  delete the obsolete inversion docstring; retarget 2 consumer imports; regen barrel.
- **Migration cost:** XS (1 move, ~4 deleted doc lines, 2 import edits, 1 barrel regen, CI reverify);
  zero signature changes; zero new `sorry`/axiom.
- **Out of scope (spawn candidate):** audit `DiegoEmbedding.lean`'s own Foundations→Logics edge.
