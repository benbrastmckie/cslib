# Research Report: Consolidating InterSystem Lattice Subsumption/Monotonicity Redundancy

**Task**: 546 — REDUNDANCY (review 2026-07-23, M2)
**Scope**: `Cslib/Logics/Modal/Metalogic/InterSystem/` — 8 near-parallel files (~893 lines)
**Zero-sorry status**: all 8 files currently sorry-free; must remain so.

## Executive Summary

The task offers two consolidation routes. Research finds that **the two options are not
independent, and neither yields a low-risk large line reduction as literally framed**:

- **Option (a)** (migrate the intuitionistic/minimal/constructive axiom *families* onto
  `SchemaUnion`) is the documented intent but is a **large multi-phase migration** touching
  **~370 constructor-`match` arms across 12 home-file axiom inductives** (soundness, forcing,
  truth-lemma, completeness proofs) — comparable in scope to the classical 8-phase SchemaUnion
  rollout. It carries real zero-debt risk and its advertised "shrinks the Lindenbaum/prime-theory
  scaffolding" benefit is **overstated** (predicate migration does not automatically collapse
  completeness-proof scaffolding).

- **Option (b)** (a "track-generic subsumption/monotonicity combinator parameterized over the
  axiom-tag type") is **not independently realizable in Lean without a shared carrier** — a
  single generic function mapping "same-named constructor of inductive X to same-named
  constructor of inductive Y" cannot be written over distinct inductive types without reflection.
  The only shared carrier that makes subsumption generic *is* `SchemaUnion`, so (b) collapses
  into (a) for the subsumption layer.

**Recommendation**: Present the decision to the user. The genuinely tractable, zero-debt-safe,
low-risk consolidation is a **confined refactor** (Recommendation R1 below): merge the 4
Subsumption + 4 Monotonicity files into fewer files and shorten the mechanical `match`
boilerplate to a one-line tactic, shrinking the "8 near-parallel files" surface the review
flagged without touching any home-file proof. If the full documented intent (a) is desired, it
**must be decomposed into a multi-phase plan** (Recommendation R2), not attempted in one
dispatch.

## Reuse Check (CSLib reuse-first protocol)

The classical generic mechanism already exists and is the model the task points at:

| Component | Location | Role |
|-----------|----------|------|
| `SchemaUnion` combinator | `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean:146` | `∃ t ∈ S, t.Holds χ` axiom predicate over a `Finset ModalSchemaTag` |
| `SchemaUnion.subsumption` | `SchemaUnion.lean:155` | the single generic subsumption lemma (`Sa ⊆ Sb → SchemaUnion Sa φ → SchemaUnion Sb φ`) |
| `SchemaUnion.{empty,insert,union}_iff` | `SchemaUnion.lean:170-204` | `@[simp]` elimination API replacing raw `fin_cases`/`match` at destructuring sites |
| `ModalSchemaTag` (18-tag alphabet) | `SchemaUnion.lean:67` | classical schema tags |
| per-system tag sets + `holds*` helpers | `SchemaTags.lean:57-193` | `kCore`, 15 tag sets, 13 witness one-liners |
| classical `AxiomSubsumption.lean` | `InterSystem/AxiomSubsumption.lean:87-200` | 24 edges, **each one line** `SchemaUnion.subsumption (by decide) h` |
| generic `Derivable_mono` / `liftDerivation` | `InterSystem/Lifting.lean:62-88` | already-generic Derivable-level lift, reused by all 4 Monotonicity files |

Key existing-intent flag: `SchemaUnion.lean:44-48` explicitly scopes the non-classical families
**out**: "`ModalSchemaTag` / `SchemaUnion` stay free of classical-only assumptions: the
intuitionistic/minimal axiom families are a possible future instance of this same abstraction,
not generalized to cover them here (out of scope for this task)." The task's option (a) is
exactly the realization of this deferred intent.

## Architectural Finding: Why the Non-Classical Families Are Not Drop-In

The classical migration worked because each `<Sys>Axiom` became
`abbrev <Sys>Axiom := SchemaUnion sysTags` (definitionally equal, so every edge is a
`decide`-able `Finset.subset`). The 12 non-classical predicates are **plain inductives with
named constructors** (`CK.lean:104 inductive CKModalAxiom`, `MK.lean:68`, `IK.lean:75`, …),
pattern-matched pervasively.

Two obstacles beyond the classical case:

1. **Constructor alphabet mismatch.** The non-classical families use constructors absent from
   the 18-tag `ModalSchemaTag`: `kdia`, Fischer-Servi `cd`/`idb`, `dbot`, and — critically —
   the modal schemata are **split into box/diamond pairs** (`tBox`/`tDia`, `fourBox`/`fourDia`,
   `bBox`/`bDia`), unlike the classical single `modalT`/`modalFour`/`modalB`. They also lack
   `peirce` and `diaDualityFwd`/`diaDualityBack`. So option (a) requires either **extending
   `ModalSchemaTag` with ~9 new tags** (violating the deliberate classical-only design invariant
   and mixing alphabets) or a **parallel non-classical tag type + parallel SchemaUnion**.

2. **Break surface.** Redefining the 12 inductives as `SchemaUnion` abbrevs breaks every
   constructor `match` in their home files. Measured surface:

   | Base | Files | Constructor-match arms |
   |------|-------|------------------------|
   | Constructive (CK/CT/CS4/CS5) | 4 | 130 |
   | Minimal (MK/MT/MS4/MS5) | 4 | 112 |
   | Intuitionistic (IK/IT/IS4/IS5) | 4 | 128 |
   | **Total** | **12** | **~370** |

   Each arm (soundness, Kripke forcing, truth-lemma, completeness) would need rewriting to the
   `simp [SchemaUnion.insert_iff, …]`-then-`rcases` disjunction form the classical elimination
   API provides. `IntToClassical.lean` (786 lines, task 484's cross-track bridge, 40 axiom
   references) is an additional consumer that would need re-checking.

This is why (a) is the classical rollout's scale again, not a small edit.

## Why Option (b) Is Not Independently Realizable

The 4 Subsumption files' proofs are all the same shape: `match h with | .ctor a b => .ctor a b`
mapping constructor `c` of the weaker inductive to the same-named constructor `c` of the
stronger inductive (`ConstructiveLatticeSubsumption.lean:53-64`, `MinimalLatticeSubsumption.lean:46-58`,
`IntuitionisticLatticeSubsumption.lean:46-60`, `PropositionalStrengthSubsumption.lean:68-227`).

A "combinator parameterized over the axiom-tag type" that erases this per-constructor map cannot
exist over two *distinct inductive types* — Lean has no term-level reflection over constructor
names. The only way to make subsumption generic is to give the families a **shared carrier
indexed by a tag `Finset`** and prove one `subsumption` lemma over `⊆` — which is precisely
`SchemaUnion`. Hence **(b)'s subsumption layer is (a)**. A "bridge-only" variant (keep the
inductives, add `NCSchemaUnion` + per-system `<Sys>Axiom φ ↔ NCSchemaUnion tags φ` bridges, route
edges through the generic lemma) does **not** reduce boilerplate: it pays one `match` case-split
per system per direction (~24 case-splits) to save 17 already-one-block edge proofs — a net
increase.

The Monotonicity layer, by contrast, is **already** the "instantiate a generic combinator"
pattern: all 4 files are thin `Derivable_mono (fun _ => <edge>) h` instantiations
(`Lifting.lean:81`), plus transitive-chain corollaries and frame-condition inclusions. There is
little to factor there — the generic combinator already exists and is reused.

## Consumer / Blast-Radius Map

| File | Lines | Imported by |
|------|-------|-------------|
| ConstructiveLatticeSubsumption | 108 | ConstructiveLatticeMonotonicity only |
| IntuitionisticLatticeSubsumption | 110 | IntuitionisticLatticeMonotonicity only |
| MinimalLatticeSubsumption | 104 | MinimalLatticeMonotonicity only |
| PropositionalStrengthSubsumption | 230 | PropositionalStrengthMonotonicity only |
| ConstructiveLatticeMonotonicity | 88 | (none) |
| IntuitionisticLatticeMonotonicity | 84 | Modularity.lean |
| MinimalLatticeMonotonicity | 83 | (none) |
| PropositionalStrengthMonotonicity | 86 | Modularity.lean |

- Each Subsumption file is imported **only** by its matching Monotonicity file.
- The subsumption **lemma names** (`CKModalAxiom_implies_CTModalAxiom`, etc.) are used **nowhere
  outside InterSystem/** — they are purely internal to the Monotonicity instantiations. This
  means merging/renaming within InterSystem/ is safe; only `Modularity.lean` and the barrel
  `Cslib.lean` reference the Monotonicity files' public theorem names.
- Consolidation therefore has a **small, contained blast radius** (InterSystem/ + `Cslib.lean`
  barrel + `Modularity.lean` imports), independent of which option is chosen.

## Candidate Proof-Shortening (verify before relying on)

Each `match | .ctor args => .ctor args` arm maps to a target whose same-named constructor has an
identical, unique proposition head-shape. A single tactic `by cases h <;> constructor` (or
`by rintro …` variants) is a strong candidate to collapse each 11–18-line `match` to **one
line**, because after `cases h` the goal's proposition shape uniquely determines the target
constructor `constructor` selects. This is **unverified** (LSP not exercised in this dispatch);
the implementer MUST confirm via `lean_multi_attempt` on each of the 4 files before adopting it,
and fall back to the explicit `match` if `constructor` mis-selects. This optimization is
orthogonal to file-merging and applies under either option.

## Recommendations

### R1 — Confined consolidation (RECOMMENDED default; low-risk, zero-debt-safe)

Do **not** migrate home-file inductives. Instead, within InterSystem/ only:

1. Merge the three same-base Subsumption files (Constructive/Minimal/Intuitionistic, each 3
   edges) into a single `LatticeSubsumption.lean` with one shared docstring; keep
   `PropositionalStrengthSubsumption.lean` (cross-base, 8 edges) as-is or merge alongside.
2. Correspondingly merge the three same-base Monotonicity files into `LatticeMonotonicity.lean`.
3. Apply the `cases h <;> constructor` shortening (R-candidate above) if verified.
4. Preserve every public lemma/theorem name verbatim (they are referenced by `Modularity.lean`
   and the barrel); update `Cslib.lean` via `lake exe mk_all --module` and re-point
   `Modularity.lean` / Monotonicity imports.

Outcome: 8 files → ~3–4 files, ~893 → ~450–550 lines, **zero home-file proof churn**, sorry-free
preserved trivially. Directly answers the review's "8 near-parallel files" flag.

### R2 — Full documented-intent migration onto SchemaUnion (HIGH value, HIGH risk)

If the user wants the documented `SchemaUnion.lean:44-48` intent realized, it **must** be a
multi-phase plan mirroring the classical rollout, decomposed as (indicative):

- Phase 1: introduce non-classical tag alphabet + combinator (either extend `ModalSchemaTag` or
  add a parallel `NCModalSchemaTag`/`NCSchemaUnion` with its own `subsumption` + elimination
  API). **Decide the alphabet question first** — it is the pivotal design decision (box/diamond
  split, `cd`/`idb`/`dbot`/`kdia`).
- Phase 2: per-system tag sets (`ckTags`, …, `is5Tags`) + `holds*` witness helpers.
- Phases 3–5: redefine each of the 12 `<Sys>ModalAxiom` as `abbrev := (NC)SchemaUnion sysTags`,
  one base-track per phase, rewriting the ~370 home-file match arms via the elimination API.
- Phase 6: collapse the 4 InterSystem Subsumption files to `decide`-based one-liners (as
  `AxiomSubsumption.lean` already is); Monotonicity files stay as thin `Derivable_mono`
  instantiations.
- Phase 7: re-verify `IntToClassical.lean` and full-project `lake build` + `lake lint`.

This is a large effort. The task's claim that it "shrinks the parallel Lindenbaum/prime-theory
scaffolding duplication between the Intuitionistic and Minimal tracks" is **not a free
byproduct**: those are completeness constructions in the home dirs (`Minimal/MinExtension.lean`,
`Intuitionistic/PrimeTheory.lean`), and axiom-predicate representation change does not by itself
merge them — flag this expectation to the user as a **separate future task**, not part of (a).

### Zero-Debt / Blocker Guidance

Neither option requires `sorry` or new axioms; do not introduce either. R1 is proof-preserving.
If R2 is chosen and any home-file match-arm rewrite cannot be discharged sorry-free, mark that
phase `[BLOCKED]` per plan-compliance rules rather than deferring with `sorry`.

## Open Questions for Planning

1. **Which option?** R1 (confined, recommended) vs R2 (full migration). Needs a user decision —
   the two differ by ~10x in scope and risk.
2. If R2: **extend `ModalSchemaTag` or add a parallel non-classical tag type?** The box/diamond
   schema split and Fischer-Servi tags make a parallel type cleaner and preserve the classical
   alphabet's design invariant.
3. Should `PropositionalStrengthSubsumption` (cross-base, 8 edges) be merged with the same-base
   files or kept separate given its distinct role?

## References

- `Cslib/Logics/Modal/ProofSystem/SchemaUnion.lean` (esp. `:44-48` scope note, `:146`, `:155`, `:170-204`)
- `Cslib/Logics/Modal/ProofSystem/SchemaTags.lean` (`:57-193`)
- `Cslib/Logics/Modal/Metalogic/InterSystem/AxiomSubsumption.lean` (classical one-liner template)
- `Cslib/Logics/Modal/Metalogic/InterSystem/Lifting.lean` (`Derivable_mono` `:81`)
- The 8 target files + home inductives `Constructive/CK.lean:104`, `Minimal/MK.lean:68`, `Intuitionistic/IK.lean:75`
