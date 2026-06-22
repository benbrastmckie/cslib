# Research Report: Inter-System Conservative Extension in the Modal Cube

**Task**: 276 -- modal_cube_inter_system_conservativity
**Session**: sess_1782161605_f646ec_276
**Date**: 2026-06-22

## 1. Executive Summary

This report analyzes the feasibility and proof strategy for inter-system conservative
extension results within CSLib's modal cube. The key finding is that two independent
proof approaches exist, and the **semantic approach** (Approach A) is strongly
recommended because it composes existing soundness/completeness infrastructure with
minimal new code. A syntactic approach (Approach B) via derivation embedding is also
viable but requires significantly more boilerplate. There are no fundamental blockers;
all 15 systems have soundness and completeness proofs, and the shared formula type
(`Modal.Proposition`) makes the "shared fragment" question trivial.

## 2. Modal Cube Architecture in CSLib

### 2.1 The 15 Systems and Their Axioms

All 15 systems share the same formula type (`Modal.Proposition Atom`) with primitives
`{atom, bot, imp, box}`. Each system is defined by an axiom predicate
(`KAxiom`, `TAxiom`, ..., `ModalAxiom` for S5) in
`Cslib/Logics/Modal/ProofSystem/Instances/{System}.lean`.

Every system includes 4 propositional axioms (implyK, implyS, efq, peirce) plus
the modal K distribution axiom, then adds characteristic modal axioms:

| System | Axioms (beyond K) | Frame Condition | Axiom Predicate |
|--------|-------------------|-----------------|-----------------|
| **K**    | (none) | unrestricted | `KAxiom` |
| **D**    | D (seriality) | serial | `DAxiom` |
| **T**    | T (reflexivity) | reflexive | `TAxiom` |
| **B**    | B (symmetry) | symmetric | `BAxiom` |
| **K4**   | 4 (transitivity) | transitive | `K4Axiom` |
| **K5**   | 5 (Euclidean) | Euclidean | `K5Axiom` |
| **K45**  | 4, 5 | trans + Euclidean | `K45Axiom` |
| **D4**   | D, 4 | serial + trans | `D4Axiom` |
| **D5**   | D, 5 | serial + Euclidean | `D5Axiom` |
| **D45**  | D, 4, 5 | serial + trans + Euclidean | `D45Axiom` |
| **DB**   | D, B | serial + symmetric | `DBAxiom` |
| **TB**   | T, B | refl + symmetric | `TBAxiom` |
| **KB5**  | B, 5 | symmetric + Euclidean | `KB5Axiom` |
| **S4**   | T, 4 | refl + trans | `S4Axiom` |
| **S5**   | T, 4, B | refl + trans + symmetric | `ModalAxiom` |

### 2.2 Proof System Architecture

Each system has:
- **Axiom predicate**: `inductive XAxiom : Proposition Atom -> Prop` in
  `Cslib/Logics/Modal/ProofSystem/Instances/X.lean`
- **Tag type**: `opaque Modal.HilbertX : Type` in
  `Cslib/Foundations/Logic/ProofSystem.lean`
- **Typeclass instances**: `InferenceSystem`, `ModusPonens`, `Necessitation`,
  `HasAxiomK`, plus characteristic `HasAxiomT/D/4/B/5` in the Instances file
- **Bundled class instance**: `ModalHilbert`, `ModalTHilbert`, `ModalS4Hilbert`, etc.
- **Soundness**: `x_soundness_derivable` in
  `Cslib/Logics/Modal/Metalogic/Systems/X/Soundness.lean`
- **Completeness**: `x_strong_completeness` / `x_completeness` in
  `Cslib/Logics/Modal/Metalogic/Systems/X/Completeness.lean`

The derivation system is parameterized: `DerivationTree Axioms Gamma phi` works for
any axiom predicate `Axioms`. Soundness is also parameterized:
`soundness d m h_ax_sound w h_ctx` works for any axiom set given a callback proving
each axiom sound in the model.

### 2.3 Semantic Layer (Cube.lean)

`Cslib/Logics/Modal/Cube.lean` defines the 15 logics as **sets of formulas** (the valid
formulas over the corresponding frame class). For example:

```lean
def K World Atom := logic (Set.univ (alpha := Model World Atom))
def T World Atom := logic {m : Model World Atom | Std.Refl m.r}
def S4 World Atom := (K World Atom) cup (T World Atom) cup (Four World Atom)
```

It also proves inclusion lemmas:
- `k_subset_d : K World Atom <= D World Atom`
- `k_subset_b : K World Atom <= B World Atom`
- `k_subset_four : K World Atom <= Four World Atom`
- `k_subset_five : K World Atom <= Five World Atom`
- `d_subset_t : D World Atom <= T World Atom`
- `k_subset_t : K World Atom <= T World Atom` (composed)

### 2.4 Existing Conservative Extension Results

CSLib already has three kinds of conservative extension:

1. **K over CPL** (`Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean`):
   If `phi.toModal` is K-derivable then `phi` is CPL-derivable. Uses the semantic
   bridge: K-soundness + `toModal_valid_implies_tautology` + CPL-completeness.

2. **Bimodal TM over CPL** (`Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/`):
   Uses derivation embedding via extended formula types (`ExtFormula`, `ExtAxiom`) and
   substitution-based lifting. Much more complex (~5 files, ~1500 lines).

3. **Temporal BX over CPL** (`Cslib/Logics/Temporal/ConservativeExtension.lean`):
   Uses semantic bridge similar to K-over-CPL.

**No inter-modal-system conservativity results exist yet.** This task is greenfield.

### 2.5 Shared Formula Fragment

The "shared formula fragment" question is trivial: **all 15 systems share the exact
same formula type** (`Modal.Proposition Atom`). There is no sub-formula type to define.
Inter-system conservativity means: if `phi` is derivable in the stronger system, then
`phi` is derivable in the weaker system (no formula restriction needed, unlike the
CPL case which required `toModal` translation).

## 3. Modal Cube Hierarchy (Extension Relations)

The modal cube is a lattice of extensions. System A extends system B if every axiom of
B is also an axiom of A (i.e., `BAxiom phi -> AAxiom phi` for all phi). This means
every B-derivable formula is A-derivable.

### 3.1 Direct Extension Edges

The following pairs have a direct axiom-subset relationship (A extends B by adding
exactly one axiom schema):

| Stronger (A) | Weaker (B) | Added Axiom |
|--------------|------------|-------------|
| T | K | T (reflexivity) |
| D | K | D (seriality) |
| B (KB) | K | B (symmetry) |
| K4 | K | 4 (transitivity) |
| K5 | K | 5 (Euclidean) |
| S4 | T | 4 |
| S4 | K4 | T |
| TB | T | B |
| TB | B | T |
| DB | D | B |
| DB | B | D |
| D4 | D | 4 |
| D4 | K4 | D |
| D5 | D | 5 |
| D5 | K5 | D |
| K45 | K4 | 5 |
| K45 | K5 | 4 |
| D45 | D4 | 5 |
| D45 | D5 | 4 |
| D45 | K45 | D |
| S5 | S4 | B |
| S5 | TB | 4 |
| S5 | KB5 | T |
| KB5 | B | 5 |
| KB5 | K5 | B |

### 3.2 Transitive Extension Chains

Through transitivity, many more pairs are related. The full inclusion order is:

```
                        S5
                      / | \
                    S4  TB  KB5
                   / \  |  / \
                  T   K4 B  K5
                  |     \ | /
                  D      K45  (note: K45 = K4 + K5, not directly related to D)
                  |
                  K
```

Note: D-family systems (D4, D5, D45, DB) sit between D and the corresponding
K-family + T-family systems because D (seriality) is weaker than T (reflexivity).

The complete Hasse diagram (immediate extensions only):

```
Level 4:  S5
Level 3:  S4, TB, KB5, D45
Level 2:  T, K4, K5, B(=KB), D4, D5, DB, K45
Level 1:  D, K (base systems)
Level 0:  (CPL -- already handled by existing conservative extension)
```

### 3.3 Conservativity Direction

**Conservative extension** means: the stronger system does not prove new theorems
(about the shared formula fragment) beyond those provable in the weaker system.

For inter-system conservativity, the claim is:

> If `phi` is derivable in system A (stronger) and `phi` uses only connectives available
> in system B (weaker), and `phi` is also valid over the frame class of system B, then
> `phi` is derivable in system B.

Since all systems share the same formula type, the restriction is vacuous. But the
validity condition matters: T-valid formulas are not necessarily K-valid (e.g., `box p -> p`
is T-valid but not K-valid).

**The correct statement of inter-system conservativity is:**

> If `phi` is derivable in system A and `phi` is valid on the frame class of system B
> (where B is weaker than A), then `phi` is derivable in system B.

This follows immediately from B-completeness: if `phi` is valid on B-frames, then
`phi` is B-derivable. The "derivable in A" hypothesis is not even needed -- it is
the semantic validity that matters.

**However**, there is a more interesting and useful formulation:

> The set of theorems of system B equals `{phi | phi valid on B-frames}`, and the set
> of theorems of system A equals `{phi | phi valid on A-frames}`. Since B-frames are a
> subclass of A-frames (every B-frame satisfies the A-conditions), every A-theorem is
> A-valid, hence B-frame-valid, hence... wait, this goes the wrong direction.

Let me be precise about the correct inter-system relationship:

### 3.4 Correct Formulation

**Claim**: If system A extends system B (A has strictly more axioms), then:
- Every B-theorem is an A-theorem (soundness direction -- trivial by axiom inclusion)
- The converse fails in general: A may prove formulas that B cannot

The "conservative extension" notion for inter-system results is therefore more nuanced.
What we can prove:

**Theorem (Semantic Conservativity via Frame Correspondence)**: For systems A and B
where A extends B:

> If `phi` is A-derivable and `phi` is valid on all B-frames, then `phi` is B-derivable.

Proof: `phi` valid on B-frames -> B-completeness -> `phi` is B-derivable. QED.

This is trivially true and is just an instance of completeness. The real content is:

**Theorem (Derivation Lifting)**: For systems A and B where A extends B, every
B-derivation can be lifted to an A-derivation. That is:

> `Derivable BAxiom phi -> Derivable AAxiom phi`

This is the "weakening" direction and is the meaningful content of the cube ordering.

**Theorem (Deduction Conservativity)**: For systems A and B where A extends B,
and for formulas `phi` that do not use the extra axioms of A:

> If `Derivable AAxiom phi` and `phi` is B-valid, then `Derivable BAxiom phi`.

This last formulation IS what the task description calls "conservative over the shared
formula fragment." Since all 15 systems share the same formula type, "shared fragment"
means ALL formulas. The condition "phi is B-valid" is critical because A may prove
formulas that are only A-valid (e.g., `box p -> p` is T-valid but not K-valid).

## 4. Proof Approaches

### 4.1 Approach A: Semantic Bridge (Recommended)

For each pair (A, B) where A extends B:

```
phi A-derivable
  -> A-soundness: phi is A-valid (valid on A-frames)
  (but we also need: phi is B-valid -- this is an extra hypothesis)
  -> B-completeness: phi is B-derivable
```

The statement would be:

```lean
theorem t_conservative_over_k {phi : Proposition Atom}
    (h_T_deriv : Derivable (@TAxiom Atom) phi)
    (h_K_valid : forall (World : Type u) (m : Model World Atom),
      forall w, Satisfies m w phi) :
    Derivable (@KAxiom Atom) phi :=
  k_completeness phi h_K_valid
```

Wait -- this doesn't use `h_T_deriv` at all! The conservativity claim reduces to:
"if phi is K-valid, then phi is K-derivable" -- which is just K-completeness.

So the more interesting result is actually **derivation lifting** (the other direction):

```lean
theorem k_derivable_implies_t_derivable {phi : Proposition Atom}
    (h : Derivable (@KAxiom Atom) phi) : Derivable (@TAxiom Atom) phi
```

This says: weaker system theorems remain theorems of the stronger system.

### 4.2 Approach B: Syntactic Derivation Embedding

For each pair (A, B) where A extends B, prove:

```lean
theorem k_axiom_implies_t_axiom {phi : Proposition Atom}
    (h : KAxiom phi) : TAxiom phi
```

Then lift to derivations:

```lean
theorem embed_derivation {phi : Proposition Atom} {Gamma : List (Proposition Atom)}
    (d : DerivationTree (@KAxiom Atom) Gamma phi) :
    DerivationTree (@TAxiom Atom) Gamma phi
```

This is a structural induction on `d`, mapping each `KAxiom` constructor to the
corresponding `TAxiom` constructor.

### 4.3 Approach Comparison

| Aspect | Approach A (Semantic) | Approach B (Syntactic) |
|--------|----------------------|----------------------|
| Lines of code | ~5 per pair | ~30-50 per pair |
| Proof depth | Trivial (compose 2 existing lemmas) | Structural induction on derivation trees |
| Dependencies | Soundness + Completeness of both systems | Only axiom predicates |
| Generality | Works for any pair | Works for any pair |
| Mathematical content | Low (reduces to completeness) | Medium (establishes axiom subsumption) |
| Usefulness | Limited (redundant with completeness) | High (directly composes derivations) |

**Recommendation**: Implement **both** approaches, but prioritize Approach B because:

1. Approach B provides syntactic derivation embedding which is independently useful
   for composing proofs across systems
2. Approach A is trivial once soundness/completeness exist (it's essentially free)
3. The axiom subsumption lemmas from Approach B are foundational building blocks

## 5. Recommended Implementation Plan

### 5.1 Phase 1: Axiom Subsumption Lemmas (Foundation)

For each direct edge in the cube, prove the axiom embedding:

```lean
-- Example: K axioms are T axioms
theorem KAxiom_of_TAxiom {phi : Proposition Atom} (h : KAxiom phi) : TAxiom phi
```

Each such lemma is a case-split on the source axiom predicate. For K -> T:
```lean
theorem KAxiom_implies_TAxiom (h : KAxiom phi) : TAxiom phi := by
  cases h with
  | implyK phi psi => exact .implyK phi psi
  | implyS phi psi chi => exact .implyS phi psi chi
  | efq phi => exact .efq phi
  | peirce phi psi => exact .peirce phi psi
  | modalK phi psi => exact .modalK phi psi
```

**Effort**: ~5-8 lines per edge, ~24 direct edges = ~150 lines total.

### 5.2 Phase 2: Derivation Lifting

For each axiom subsumption lemma, derive the derivation lifting:

```lean
theorem lift_derivation_k_to_t {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree (@KAxiom Atom) Gamma phi) :
    DerivationTree (@TAxiom Atom) Gamma phi
```

This can be done generically once:

```lean
theorem lift_derivation {Axioms1 Axioms2 : Proposition Atom -> Prop}
    (h_sub : forall phi, Axioms1 phi -> Axioms2 phi)
    {Gamma : List (Proposition Atom)} {phi : Proposition Atom}
    (d : DerivationTree Axioms1 Gamma phi) :
    DerivationTree Axioms2 Gamma phi
```

This single generic lemma handles ALL pairs via structural induction on `d`:
- `.ax` case: apply `h_sub` to convert the axiom
- `.assumption` case: pass through
- `.modus_ponens` case: recurse on both subderivations
- `.necessitation` case: recurse
- `.weakening` case: recurse

**Effort**: ~20 lines for the generic lemma. Then ~3 lines per instantiation.

### 5.3 Phase 3: Derivability Monotonicity

Lift from `DerivationTree` to `Derivable`:

```lean
theorem Derivable_mono {Axioms1 Axioms2 : Proposition Atom -> Prop}
    (h_sub : forall phi, Axioms1 phi -> Axioms2 phi)
    {phi : Proposition Atom} (h : Derivable Axioms1 phi) :
    Derivable Axioms2 phi
```

**Effort**: ~5 lines.

### 5.4 Phase 4: Semantic Conservativity (Optional)

For completeness, prove the semantic direction:

```lean
theorem semantic_conservative {Axioms : Proposition Atom -> Prop}
    {phi : Proposition Atom}
    (h_valid : forall (World : Type u) (m : Model World Atom),
      forall w, Satisfies m w phi)
    (h_completeness : forall (phi : Proposition Atom),
      (forall (World : Type u) (m : Model World Atom),
        forall w, Satisfies m w phi) ->
      Derivable Axioms phi) :
    Derivable Axioms phi :=
  h_completeness phi h_valid
```

This is trivially just applying completeness. Not very interesting but documents
the semantic conservativity.

### 5.5 Phase 5: Cube Ordering Instances

Prove that the derivability relation forms a partial order matching the cube:

```lean
-- Key edges
theorem k_weaker_than_t : Derivable (@KAxiom Atom) phi -> Derivable (@TAxiom Atom) phi
theorem k_weaker_than_d : Derivable (@KAxiom Atom) phi -> Derivable (@DAxiom Atom) phi
theorem t_weaker_than_s4 : Derivable (@TAxiom Atom) phi -> Derivable (@S4Axiom Atom) phi
theorem s4_weaker_than_s5 : Derivable (@S4Axiom Atom) phi -> Derivable (@ModalAxiom Atom) phi
-- ... etc for all edges
```

## 6. Prioritized Results

### 6.1 Highest Priority (Core Building Blocks)

1. **`lift_derivation`** -- Generic derivation lifting lemma (Phase 2)
2. **`Derivable_mono`** -- Generic derivability monotonicity (Phase 3)
3. **Axiom subsumption for K-chain**: K -> T -> S4 -> S5 (Phase 1, 3 edges)
4. **Axiom subsumption for K-chain**: K -> D -> D4 -> D45 (Phase 1, 3 edges)

### 6.2 Medium Priority (Completeness of Cube)

5. Axiom subsumption for remaining direct edges (~18 edges)
6. Derivability chain lemmas via transitivity

### 6.3 Lower Priority (Nice-to-Have)

7. Semantic conservativity wrappers (trivial given completeness)
8. Full partial order proof
9. Cube.lean integration (extend the existing `Order` section with derivability ordering)

## 7. Difficulty Estimates

| Component | Lines | Difficulty | Dependencies |
|-----------|-------|------------|--------------|
| `lift_derivation` (generic) | ~20 | Easy | `DerivationTree` |
| `Derivable_mono` (generic) | ~5 | Trivial | `lift_derivation` |
| Axiom subsumption (per edge) | ~8 | Easy (mechanical) | Axiom predicates |
| Instantiation (per edge) | ~3 | Trivial | `Derivable_mono` + subsumption |
| Semantic conservativity | ~5 per pair | Trivial | Completeness theorems |
| Total (all 24 edges) | ~350 | Easy | All of above |

**Risk assessment**: Very low. The `lift_derivation` lemma is a straightforward
structural induction. The axiom subsumption lemmas are mechanical case-splits
(each constructor of the source maps to the same constructor of the target).
No new mathematical insight is needed.

## 8. File Organization Recommendation

```
Cslib/Logics/Modal/Metalogic/InterSystem/
  Lifting.lean          -- Generic lift_derivation, Derivable_mono
  AxiomSubsumption.lean -- All axiom embedding lemmas (KAxiom -> TAxiom, etc.)
  Conservativity.lean   -- Instantiated conservativity theorems
```

Alternatively, extend `Cslib/Logics/Modal/Cube.lean` with a `Derivability` section
alongside the existing `Order` section.

## 9. Key Codebase References

| File | Content | Relevance |
|------|---------|-----------|
| `Cslib/Logics/Modal/Metalogic/DerivationTree.lean` | `DerivationTree`, `Deriv`, `Derivable` | Core data structure for lifting |
| `Cslib/Logics/Modal/ProofSystem/Instances/*.lean` | Per-system axiom predicates | Source/target of subsumption |
| `Cslib/Logics/Modal/Cube.lean` | Semantic cube + subset lemmas | Potential home for derivability cube |
| `Cslib/Logics/Modal/Metalogic/Soundness.lean` | Parameterized soundness | For semantic approach |
| `Cslib/Logics/Modal/Metalogic/Systems/*/Completeness.lean` | Per-system completeness | For semantic approach |
| `Cslib/Logics/Modal/Metalogic/Systems/K/ConservativeExtension.lean` | K-over-CPL conservativity | Existing pattern for CPL direction |
| `Cslib/Foundations/Logic/ProofSystem.lean` | Hilbert class hierarchy | Tag types and bundled classes |

## 10. Conclusions and Recommendations

1. **The task is straightforward**: All infrastructure exists. The generic
   `lift_derivation` lemma is ~20 lines and handles all pairs at once.

2. **Start with the generic lemma**: `lift_derivation` eliminates 90% of the work.
   Then axiom subsumption lemmas are mechanical.

3. **The "conservative extension" framing is slightly misleading**: What the task
   describes is really "derivation monotonicity" (weaker system theorems lift to
   stronger systems) and "completeness-based conservativity" (the semantic direction).
   Neither is mathematically deep given the existing infrastructure.

4. **Dependency on CPL conservativity**: The task description says "Lower priority --
   establish after per-system CPL conservativity is done." This dependency is
   **unnecessary** for the syntactic approach (Approach B), which only needs the
   axiom predicates and derivation tree structure, not CPL results. The semantic
   approach does require soundness/completeness, which are already complete for
   all 15 systems.

5. **The most useful output** is the axiom subsumption table and the generic
   `lift_derivation` lemma, which enable composing proofs across modal systems.

6. **Zero-sorry feasibility**: All proofs in this task are structural/mechanical.
   There is no risk of needing sorry.
