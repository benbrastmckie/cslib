# Task 243: Deterministic Büchi Automata — Research Report

## Task Description

Implement deterministic Büchi automata constructions and related results.

## 1. Existing CSLib Infrastructure

### 1.1 DBA Definition and Basic Results (Already Implemented)

The DBA infrastructure is more developed than the task description suggests. The following
are already implemented and sorry-free:

| File | Contents | Lines |
|------|----------|-------|
| `DA/Basic.lean` | `DA` structure (FLTS + start), `DA.run`, `DA.Buchi` structure, `DA.Muller` structure, `DA.FinAcc` structure | 123 |
| `DA/Buchi.lean` | `buchi_eq_finAcc_omegaLim`: DBA language = ω-limit of DFA language | 32 |
| `DA/Prod.lean` | `DA.prod`: product of two DAs, `prod_mtr_eq` | 42 |
| `DA/Congr.lean` | `RightCongruence.toDA`: DA from right congruence, `congr_language_eq` | 72 |
| `DA/ToNA.lean` | `DA.toNA`, `DA.Buchi.toNABuchi`, `toNABuchi_language_eq`, `DA.FinAcc.toNAFinAcc`, `toNAFinAcc_language_eq` | 97 |

### 1.2 DBA Results in OmegaRegularLanguage.lean (Already Implemented)

The key DBA theorems are already proved:

| Theorem | Statement | Status |
|---------|-----------|--------|
| `IsRegular.of_da_buchi` | DBA language is ω-regular | Done |
| `IsRegular.not_da_buchi` | There exists an ω-regular language not accepted by any DBA (even infinite-state) | Done |
| `eventuallyZero_not_omegaLim` | The witness language (eventually zero) is not an ω-limit | Done |
| `IsRegular.compl` | ω-regular languages are closed under complement (via Büchi congruence) | Done |
| `IsRegular.iff_da_muller` | McNaughton's theorem: ω-regular ↔ DMA-recognizable | `proof_wanted` |

### 1.3 NBA Infrastructure (Available for DBA Constructions)

| File | Contents |
|------|----------|
| `NA/Basic.lean` | `NA`, `NA.Buchi`, `NA.Muller` structures |
| `NA/BuchiInter.lean` | NBA intersection via product + history bit toggling |
| `NA/BuchiEquiv.lean` | NBA equivalence via state reindexing |
| `NA/Emptiness.lean` | NBA emptiness characterization |
| `NA/Prod.lean`, `Sum.lean`, `Concat.lean`, `Loop.lean` | NBA closure constructions |
| `NA/ToDA.lean` | Subset construction (finite words) |

### 1.4 Supporting Infrastructure

| File | Contents |
|------|----------|
| `Acceptors/OmegaAcceptor.lean` | `ωAcceptor` typeclass, `ωLanguage`, `Accepts` |
| `Languages/OmegaLanguage.lean` | ω-language operations, ω-limit, ω-power |
| `Languages/OmegaRegularLanguage.lean` | `IsRegular`, closure under ∪, ∩, complement, concatenation, ω-power |
| `Languages/Congruences/BuchiCongruence.lean` | Büchi congruence for complementation |
| `Foundations/Data/OmegaSequence/InfOcc.lean` | `infOcc` predicate (infinitely often occurring states) |

## 2. What Remains to Be Done

Given the existing infrastructure, "DBA constructions and related results" should focus on
results that are **not yet formalized**. The candidates, ordered by significance:

### 2.1 DBA Closure Properties

**DBA union** (product construction):
- DBAs ARE closed under union (Baier & Katoen Exercise 4.23).
- Construction: product automaton with `accept = F₁ × Q₂ ∪ Q₁ × F₂`. A state visits this
  set infinitely often iff it visits F₁ × Q₂ infinitely often OR Q₁ × F₂ infinitely often
  (by pigeonhole, since the union is visited infinitely often implies at least one component is).
- Size: O(|A₁| · |A₂|). Since `DA.prod` already exists, the construction is straightforward.
- **Note**: `IsRegular.sup` already proves ω-regular closure under union via the NBA route.
  A direct DBA union proves closure *within* the DBA class.

**DBA intersection** (product construction with counter):
- DBAs are also closed under intersection, but the naive `accept = F₁ × F₂` does NOT work
  (visiting F₁ × F₂ infinitely often ≠ visiting F₁ and F₂ each infinitely often).
- Standard construction: product with 3-state counter (wait for F₁ → wait for F₂ → reset),
  same toggling trick as NBA intersection in `BuchiInter.lean` but deterministic.

**DBA complement**:
- DBAs are NOT closed under complement (Baier & Katoen Exercise 4.22).
- Proof: "infinitely many a's" is DBA-recognizable, but its complement "eventually zero"
  is not (already proved as `IsRegular.not_da_buchi` + `eventuallyZero_not_omegaLim`).

### 2.2 DBA Characterization (Landweber's Theorem)

**Characterizing DBA-recognizable languages** (Theorem 3.32 in Thomas 2003):
- An ω-regular language L (given by a Muller automaton A) is DBA-recognizable iff the
  acceptance family F is closed under superloops.
- A loop S ⊆ Q is a nonempty set where every state can reach every other state.
- F is closed under superloops iff for every F-loop S and every superloop S' ⊇ S,
  also S' ∈ F.
- This is equivalent to: L is the ω-limit of a regular language (connecting to
  `buchi_eq_finAcc_omegaLim`).
- Thomas 2003 Ch. 3 has the COMPLETE PROOF in both directions.

### 2.3 DBA Minimization / Canonical Form

- DBA minimization is NP-complete (unlike DFA minimization which is polynomial).
- Weak DBA minimization reduces to DFA minimization (Löding 2001).
- Löding 2001 paper behind paywall; construction available in outline from other sources.

### 2.4 DBA ⊆ DMA / DBA ⊆ DPA Conversions

- Every DBA is trivially a DMA: accept family F = {S ⊆ Q | S ∩ accept ≠ ∅}.
- Every DBA is a DPA with priorities {1, 2}: accepting states get priority 2 (even = good),
  non-accepting get priority 1 (odd = bad).
- These conversions are relevant to task 252 (acceptance conditions zoo).

### 2.5 Classification Hierarchy

Thomas 2003 §3.6 proves the strict hierarchy of deterministic ω-automata:

```
det. E ⊊ det. Büchi ⊊ det. co-Büchi ⊊ det. Muller (= all ω-regular)
det. A ⊊ det. co-Büchi ⊊ det. Muller
```

with concrete separating examples for each pair.

## 3. Literature Source Assessment

### 3.1 Available in Centralized Literature (LITERATURE_DIR)

| Source | Tokens | DBA Coverage | Proofs? |
|--------|--------|-------------|---------|
| **Thomas 2003** — "Automata and Reactive Systems" Ch. 3 | 10,514 | **Primary**: DBA def, classification hierarchy, Landweber's theorem (Thm 3.32) with FULL PROOF, Staiger-Wagner, exercises on DBA closure | **YES — complete proofs** |
| **Thomas 2003** — Ch. 1 | 6,056 | NBA basics, product intersection construction (with counter trick), closure properties | **YES** |
| **Thomas 1997** — "Languages, Automata, and Logic" | 45,129 | Comprehensive: DBA def, DBA < NBA limitation, Safra construction, star-free connection | **YES** (Safra proof complete) |
| **Baier & Katoen 2008** — *Principles of Model Checking* | ~480,000 | Textbook: DBA definition (4.48), Theorem 4.50 (NBA > DBA with full proof), Exercises 4.22-4.23 (closure) | **Theorem 4.50 YES; exercises NO** |
| **Piterman 2007** — "From NBA/Streett to Deterministic Parity" | 18,501 | Determinization constructions, DBA→DPA conversion | **YES** |
| **Schewe 2009** — "Büchi Complementation Made Tight" | 10,312 | Complementation bounds. DBA peripheral. | Peripheral |
| **Kupferman & Vardi 2001** — "Weak Alternating Automata" | 16,468 | Alternation hierarchy, weak DBA. | Tangential |

### 3.2 Available in specs/literature/

No DBA-specific entries. The temporal logic sources (Burgess, Gabbay, Reynolds) are not
relevant to DBA constructions.

### 3.3 Newly Acquired Source

**Thomas 2003 — "Automata and Reactive Systems" lecture notes (RWTH Aachen)**:
- Downloaded from CMI teaching repository.
- By Wolfgang Thomas (with contributions from Christof Löding).
- Chapters 1 and 3 converted and added to Literature index.
- **This is the key source**: Chapter 3 contains Landweber's Theorem (Thm 3.32) with
  complete proof in both directions, the classification hierarchy with all separating examples,
  and the Staiger-Wagner framework.

### 3.4 Sources NOT Available (Behind Paywalls)

| Source | Status | Impact |
|--------|--------|--------|
| **Landweber 1969** — "Decision problems for ω-automata" (Math. Systems Theory) | Springer paywall | Low — Thomas 2003 covers Landweber's theorem with proof |
| **Löding 2001** — "Efficient minimization of deterministic weak ω-automata" (IPL) | ScienceDirect paywall | Medium — needed only for DBA minimization (§2.3) |
| **Perrin & Pin 2004** — *Infinite Words* (Elsevier book) | Commercial book, no free PDF | Low — Thomas 2003 + Thomas 1997 cover the needed material |

### 3.5 Assessment for `--lit` Flag

**Now adequate for all recommended phases.** Thomas 2003 Ch. 3 provides complete proofs
for the Landweber characterization and classification hierarchy. Baier & Katoen provides the
DBA < NBA proof. Thomas 2003 Ch. 1 provides the intersection construction template.

The only gap is DBA minimization (Löding 2001 behind paywall), which is NP-complete
anyway and probably not a good formalization target.

## 4. Recommended Scope for Task 243

Given the existing infrastructure and available literature, the task should focus on results
that complement the already-proved theorems.

### Phase 1: DBA Closure Properties (~200–300 lines)

**DBA union** (positive closure):
```lean
def DA.Buchi.union (a₁ : DA.Buchi S₁ Σ) (a₂ : DA.Buchi S₂ Σ) :
    DA.Buchi (S₁ × S₂) Σ

theorem DA.Buchi.union_language_eq :
    language (a₁.union a₂) = language a₁ ⊔ language a₂
```
- Construction: product automaton, accept = F₁ × Q₂ ∪ Q₁ × F₂.
- Proof: pigeonhole — visiting the union infinitely often implies at least one component
  visited infinitely often.
- Source: Baier & Katoen Exercise 4.23 (construction hint), Thomas 2003 Ch. 1 (product
  construction template).

**DBA intersection** (positive closure with counter):
```lean
def DA.Buchi.inter (a₁ : DA.Buchi S₁ Σ) (a₂ : DA.Buchi S₂ Σ) :
    DA.Buchi (S₁ × S₂ × Fin 3) Σ

theorem DA.Buchi.inter_language_eq :
    language (a₁.inter a₂) = language a₁ ⊓ language a₂
```
- Construction: product with 3-state counter tracking which accepting set was last seen.
- Source: Thomas 2003 Ch. 1 §1.3 (NBA intersection with counter), adapted deterministically.

**DBA non-closure under complement**:
```lean
theorem DA.Buchi.not_closed_complement :
  ∃ (Symbol : Type) (L : ωLanguage Symbol),
    (∃ S (da : DA.Buchi S Symbol), language da = L) ∧
    ¬ ∃ S (da : DA.Buchi S Symbol), language da = Lᶜ
```
- Proof: "infinitely many a's" is DBA-recognizable; its complement "eventually zero" is
  not (`IsRegular.not_da_buchi` already provides the witness).
- Source: Baier & Katoen Theorem 4.50 + Exercise 4.22.

Target: `Cslib/Computability/Automata/DA/BuchiClosure.lean`

### Phase 2: DBA Characterization — Landweber's Theorem (~300–400 lines)

```lean
def DA.Muller.IsLoop (a : DA.Muller S Σ) (S : Set S) : Prop

def DA.Muller.ClosedUnderSuperloops (a : DA.Muller S Σ) : Prop

theorem DA.Muller.dba_recognizable_iff_closed_superloops
    [Finite S] (a : DA.Muller S Σ) :
    (∃ (acc : Set S), language (DA.Buchi.mk a.toDA acc) = language a) ↔
    a.ClosedUnderSuperloops
```

- This is the core characterization: an ω-regular language (given by a DMA) is
  DBA-recognizable iff the acceptance family is closed under superloops.
- Source: Thomas 2003 Theorem 3.32 — **complete proof in both directions**.
- Forward direction: construct DBA from DMA with superloop-closed F by accumulating
  visited states and resetting when an F-loop is hit.
- Backward direction: given a DBA recognizing L, show any superloop of an F-loop is
  also in F using the deterministic pumping argument.

Target: `Cslib/Computability/Automata/DA/BuchiChar.lean`

### Phase 3: DBA → DMA / DBA → DPA Conversions (~100–150 lines)

```lean
def DA.Buchi.toMuller (a : DA.Buchi S Σ) : DA.Muller S Σ

theorem DA.Buchi.toMuller_language_eq :
    language a.toMuller = language a
```
- Trivial: F_muller = {S ⊆ Q | S ∩ F_buchi ≠ ∅}.
- Defer to task 252 if parity acceptance is defined there.

### Estimated Total Scope

Phases 1–2: ~500–700 lines of new Lean code across 2 new files.
Phase 3: ~100–150 lines (can be deferred to task 252).

## 5. Proof Source Coverage Matrix

| Result | Source with Proof | Status |
|--------|-------------------|--------|
| DBA < NBA (∃ ω-regular not DBA-recognizable) | Baier & Katoen Thm 4.50 (full proof) | **Already in CSLib** |
| DBA language = ω-limit of DFA language | — | **Already in CSLib** (`buchi_eq_finAcc_omegaLim`) |
| DBA closed under union | Baier & Katoen Ex 4.23 (hint only); standard pigeonhole | **Construction clear, no full proof in lit** |
| DBA closed under intersection | Thomas 2003 Ch. 1 §1.3 (NBA version with counter) | **Template available, adapt to deterministic** |
| DBA not closed under complement | Baier & Katoen Ex 4.22 (follows from Thm 4.50) | **Follows from existing CSLib result** |
| DBA-recognizable ↔ superloop-closed | Thomas 2003 Thm 3.32 (FULL PROOF both directions) | **Complete proof available** |
| Classification hierarchy (E ⊊ Büchi ⊊ co-Büchi ⊊ Muller) | Thomas 2003 §3.6 (with separating examples) | **Complete with witnesses** |

## 6. Relationship to Other Tasks

| Task | Relationship |
|------|-------------|
| 241 (McNaughton's theorem) | McNaughton = DMA ↔ NBA. DBA → DMA conversion (Phase 3) is a prerequisite step. |
| 245 (Formula Encodable/Countable) | Independent. |
| 248 (NBA emptiness) | Completed. DBA emptiness is simpler (reachability in deterministic graph). |
| 250 (NBA complementation) | NBA complement uses determinization. DBA complement is trivial (swap accept). |
| 252 (Acceptance conditions zoo) | DBA → DMA / DBA → DPA conversions should live in task 252. |

## 7. Conclusion

The literature is now sufficient for all recommended phases:

- **Thomas 2003 Ch. 3** (newly acquired) provides the Landweber Theorem with complete
  proof — the most valuable missing piece.
- **Thomas 2003 Ch. 1** provides the intersection construction template.
- **Baier & Katoen 2008** provides the NBA > DBA proof (already in CSLib) and closure
  property hints.

The recommended scope focuses on: (1) DBA closure under union and intersection (positive
results with explicit constructions), (2) DBA non-closure under complement (clean corollary
of existing CSLib results), and (3) the Landweber characterization (superloop closure ↔
DBA-recognizability) which is the most substantial and valuable contribution.

**Correction from v1**: The initial report incorrectly stated DBAs are NOT closed under
union. DBAs ARE closed under union (Baier & Katoen Exercise 4.23) via the product
construction with accept = F₁ × Q₂ ∪ Q₁ × F₂.
