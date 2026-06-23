# Teammate C (Critic) Findings: Task 313 — Zulip Propositional Logic Post

**Task**: Research and compose a Zulip comment for the CSLib Propositional Logic topic  
**Role**: Critic — gaps, asymmetries, overclaiming risks, newcomer expectations  
**Date**: 2026-06-23  
**Session**: (from delegation context)

---

## Key Findings

### 1. The Task Title Is Factually Wrong: There Are Only Two Proof Systems, Not Three

The task description says "three proof systems (Hilbert, Natural Deduction, Sequent Calculus)." This is incorrect about the current state. CSLib has exactly two proof systems for propositional logic:

- **Hilbert system** (`ProofSystem/`): parameterized `DerivationTree Axioms` with three instantiations (MinPropAxiom, IntPropAxiom, PropositionalAxiom).
- **Natural Deduction** (`NaturalDeduction/`): `Theory.Derivation` with 10 primitive constructors.

**The sequent calculus does not exist yet.** Task 279 ("Implement a two-sided Gentzen-style sequent calculus") is `[NOT STARTED]`. The team research report from task 280 (`specs/archive/280_proof_system_triad_gap_analysis/reports/01_team-research.md`) explicitly states: "No LK or LJ exists for propositional logic. The only sequent calculus in CSLib is CLL (linear logic)." Confirming: no `SequentCalculus`, `LK`, `LJ`, or `CutElimination` declarations exist in `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/`.

**Implication for the Zulip post**: The post cannot present three completed systems. It must either (a) present two completed systems and one planned/in-progress system, or (b) focus on what is complete and note the roadmap for sequent calculus. Overclaiming the sequent calculus as complete would be a factual error in a public technical forum.

### 2. Significant Asymmetry: Sequent Calculus Has Zero Coverage

The three systems have radically different coverage levels:

| System | Status | Soundness | Completeness | Bridges | Decidability |
|--------|--------|-----------|--------------|---------|--------------|
| Hilbert | Complete | Yes (CPL, IPL, MPL) | Yes (strong, all three) | Yes (to ND) | Yes (CPL via tautology) |
| Natural Deduction | Core complete, proof theory gaps | Yes (via Hilbert bridge) | Yes (via Hilbert bridge) | Yes (to Hilbert) | No (IPL/MPL blocked) |
| Sequent Calculus | Non-existent | — | — | — | — |

Presenting these three as coordinate "systems" in the post would be deeply misleading. A newcomer reading the post would expect all three to be at roughly the same maturity level.

### 3. What Lean Community Members Would Expect But Not Find

A Lean community member arriving at the propositional logic namespace after reading the Zulip post would expect to find:

**For the Hilbert system** (everything is there):
- Axioms, derivation trees, MCS, deduction theorem, soundness/completeness: YES

**For Natural Deduction** (mostly there, with notable gaps):
- Basic derivation type, structural rules, Hilbert-ND bridge: YES
- **Normalization theorem (Prawitz-style)**: NO — task 290, not started
- **Subformula property**: NO — blocked on normalization
- **Curry-Howard correspondence**: NO — task 293, blocked on 290
- **ND-specific decidability**: NO — blocked on sequent calculus (task 279)

**For Sequent Calculus** (entirely missing):
- LK/LJ definition: NO
- Cut elimination (Hauptsatz): NO
- Hilbert-ND-SC three-way equivalence: NO — task 291, blocked on 279
- IPL decidability via cut-free LJ: NO — task 292, blocked on 279

If the post says "CSLib includes a sequent calculus," this is false. If it implies the ND system is fully mature proof-theoretically, that is also overclaiming. The ND system is strong as a combinatorial object but lacks the normalization machinery a proof theorist would consider essential.

### 4. Sorry Markers: Zero in Propositional Logic (This Is Genuinely Good News)

An exhaustive grep for `sorry` in `/home/benjamin/Projects/cslib/Cslib/Logics/Propositional/` returned no results. The propositional logic modules are entirely sorry-free. This is a legitimately strong claim and should be made in the Zulip post.

Similarly, no `proof_wanted` or `TODO` or `FIX:` markers appear. The two proof systems that exist are complete and clean.

**Recommendation**: The post SHOULD highlight the zero-sorry status. This is rare for a library of this scope and is a genuine differentiator from Mathlib-adjacent libraries.

### 5. Asymmetric Semantics Coverage Between Systems

A subtle asymmetry that could confuse a semantics-focused reader:

- **Hilbert system**: Has algebraic completeness (Heyting/Boolean algebra), Kripke completeness (all three tiers), Glivenko theorem, conservative extension (IPL over MPL), and bool/tautology completeness.
- **ND system**: Has algebraic completeness (via bridge to Hilbert), Kripke completeness (via bridge), but these results are derived from the Hilbert system — not proved directly for the ND formulation.

This is not a problem per se (the bridge `hilbert_iff_nd` makes the transfer legitimate), but a reader who wants to understand "what is the ND system's relationship to Kripke semantics directly" will find that the answer is "it goes through the Hilbert system." The post should not present the ND system as having independent semantic completeness proofs.

### 6. The "Three Systems" Framing Creates a Future-Commitment Problem

If the Zulip post says "CSLib covers three proof systems: Hilbert, ND, and Sequent Calculus," it creates an implicit community commitment. If task 279 is delayed or blocked (cut elimination for two-sided LK is a 300-800 line proof, per task 280's Critic analysis), the community may ask follow-up questions about progress. The post should be honest about which systems are implemented and which are planned.

A better framing: "CSLib has two mature proof systems for propositional logic, with a third (sequent calculus) in active development."

### 7. The ND Design Decision (efq as Theory Axiom, Not Constructor) Needs Framing

The Natural Deduction system made a non-standard design choice: `efq` (ex falso quodlibet, bottom elimination) is not a primitive constructor of `Theory.Derivation` but a derived rule using the theory parameter. The ND file's module header explicitly discusses this as a deliberate trade-off (uniformity across the multi-logic hierarchy vs. Gentzen-style constructor-rule correspondence).

A community member familiar with [Prawitz1965] or [TroelstraVanDalen1988] will notice this immediately and may object that it is "not standard ND." The Zulip post should acknowledge this design decision or at least not describe the system as a straightforward Gentzen-style ND without qualification.

The Zulip thread on Propositional Logic is explicitly referenced in `NaturalDeduction/Basic.lean` (line 76): "This design choice and its trade-offs are discussed further in the CSLib Zulip thread on Propositional Logic." So the community is already aware this was a design decision — the post should acknowledge it rather than silently ignoring it.

### 8. IPL Decidability Is Missing and Not Easily Obtainable

The task description suggests that the sequent calculus is "best equipped for decidability." This is true in the standard treatment (cut-free LJ gives IPL decidability via proof search termination). But the consequence is:

- CPL decidability is already present in CSLib (via `instDecidableDerivablePropositionalAxiom` using the `decidable_of_iff (Tautology phi)` approach).
- **IPL decidability is not present** and requires either: (a) a cut-free LJ (blocked on task 279), or (b) a direct model-theoretic decision procedure (non-trivial). 
- MPL decidability is similarly missing.

The post should not imply that decidability for all three logic tiers is complete. Only CPL has a `Decidable` instance.

### 9. Documentation/Module Structure: Adequate but Lacks a Top-Level README

A newcomer navigating `Cslib/Logics/Propositional/` will find well-documented individual files (module headers with main definitions, references, architecture notes). However, there is no top-level `README.lean` or analogous entry point explaining the overall structure.

`Defs.lean` serves as a partial entry point (it has the Architecture section listing Layer 1 and Layer 2), but it does not explain the Metalogic/ or Semantics/ subdirectories. A newcomer would need to read multiple files to understand the full picture.

The Zulip post itself will serve as documentation for the community — this is a positive externality. But the post should be careful not to promise a navigation experience that does not exist in-code.

---

## Recommended Approach

### What the Post SHOULD Say

1. **Frame correctly as two systems, not three**: Present Hilbert and ND as implemented, sequent calculus as in-progress (planned in task 279).
2. **Highlight zero-sorry status**: This is genuinely impressive and worth calling out.
3. **Acknowledge the efq design decision**: It is already on record in the Zulip thread; reference it explicitly.
4. **Be accurate about decidability**: CPL is decidable; IPL/MPL are not yet.
5. **Describe the Hilbert-ND bridge**: This is the most architecturally interesting result — two independently motivated systems with a proven extensional equivalence.
6. **Mention the three-tier structure (MPL/IPL/CPL)**: This is distinctive; most formalization projects only do classical or only intuitionistic.

### What the Post MUST NOT Say

1. That CSLib has three implemented proof systems (it has two).
2. That the ND system has normalization or the subformula property (it does not).
3. That IPL is decidable in CSLib (it is not).
4. That the ND system has direct Kripke completeness proofs (these go through the Hilbert bridge).

### Tone Risks

- **Overclaiming**: The biggest risk. The system is impressive but claiming three systems or full proof-theoretic coverage would be false.
- **Underclaiming**: Less likely but possible if the post is too hedged. The Hilbert system really is fully complete (strong soundness, strong completeness, compactness, Glivenko, conservative extension, algebraic semantics, Kripke semantics) — this is worth celebrating.

---

## Evidence/Examples

**Evidence that sequent calculus is absent**:
- `grep -rn "SequentCalculus\|LK\|LJ\|cut.*elim" Cslib/Logics/Propositional/` returns no results.
- Task 279 is `[NOT STARTED]` in TODO.md.
- Task 280 team research (archived) explicitly states: "The sequent calculus leg is entirely absent."

**Evidence that ND normalization is absent**:
- No `isNormal`, `normalize`, `normalization`, or `subformula` declarations in `NaturalDeduction/`.
- Task 290 ("Formalize Prawitz-style normalization") is `[NOT STARTED]`.

**Evidence that zero sorries exist**:
- `grep -rn "sorry" Cslib/Logics/Propositional/` produces no output (exit code 1, empty match).

**Evidence of the efq design decision**:
- `NaturalDeduction/Basic.lean` lines 55-76: explicit design trade-off discussion with reference to Prawitz1965, TroelstraVanDalen1988, and the Zulip thread.

**Evidence of CPL decidability but not IPL/MPL**:
- `StrongCompleteness.lean` line 566: `instDecidableDerivablePropositionalAxiom` exists for CPL.
- No analogous instance for `IntPropAxiom` or `MinPropAxiom`.

---

## Confidence Level

**High** for all findings. The codebase evidence is unambiguous:
- The sequent calculus is entirely absent.
- The sorry count is zero.
- The efq design decision is explicitly documented.
- The decidability asymmetry is easily verified.

The main uncertainty is whether task 279 is already in-flight on a branch not visible from the main branch. A brief check of git branches before posting would be prudent.
