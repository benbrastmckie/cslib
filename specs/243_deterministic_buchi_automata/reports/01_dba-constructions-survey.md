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

**DBA intersection** (product construction):
- Given two DBAs, construct a DBA accepting the intersection.
- For DBAs (unlike NBAs), intersection is straightforward: product automaton with
  `accept = accept₁ ∩ accept₂` does NOT work (need both to be visited infinitely often).
- Standard construction: product with 3-state counter (similar to NBA intersection but
  deterministic). Alternatively, since `DA.prod` already exists, the DBA intersection uses
  the same toggling trick as NBA intersection but deterministically.
- **Note**: `IsRegular.inf` already proves ω-regular languages are closed under intersection
  via the NBA route. A direct DBA intersection would show which languages are closed under
  intersection *within* the DBA class.

**DBA union**:
- DBAs are NOT closed under union in general (standard result).
- Could formalize: the union of two DBA languages is ω-regular (trivial from `of_da_buchi` + `IsRegular.sup`).
- The interesting result: DBA languages are NOT closed under union — construct a witness.

**DBA complement**:
- DBAs are NOT closed under complement (follows from `not_da_buchi`: the complement of
  "infinitely many a's" is "eventually zero" which is not DBA-recognizable).
- Could state and prove this as a clean theorem.

### 2.2 DBA Characterization

**Characterizing DBA-recognizable languages**:
- A language is DBA-recognizable iff it is a Gδ set in the Cantor topology (countable
  intersection of open sets) — equivalently, it is a "limit language" (ω-limit of a regular
  language, which `buchi_eq_finAcc_omegaLim` already connects).
- The key characterization theorem: an ω-regular language is DBA-recognizable iff it equals
  its ω-limit closure. This is the Landweber characterization.
- This would be a substantial and valuable addition.

### 2.3 DBA Minimization / Canonical Form

- Right congruence for DBA: already have `RightCongruence.toDA` and `BuchiCongruence`.
- Could develop a Myhill-Nerode-style characterization for DBA languages.

### 2.4 DBA ⊆ DMA / DBA ⊆ DPA

- Every DBA is trivially a DMA (with accept = {F | F ∩ accept ≠ ∅}).
- Every DBA is a DPA with priorities {1, 2} (accepting = priority 2, non-accepting = priority 1).
- These conversions are relevant to task 252 (acceptance conditions zoo).

## 3. Literature Source Assessment

### 3.1 Available in Centralized Literature (LITERATURE_DIR)

| Source | Tokens | DBA Coverage | Quality |
|--------|--------|-------------|---------|
| **Thomas 1997** — "Languages, Automata, and Logic" | 45,129 | DBA definition, DBA < NBA limitation, McNaughton/Safra determinization, star-free connection, Wagner hierarchy. §5.2 covers determinization in detail. | **Excellent** — comprehensive handbook reference |
| **Piterman 2007** — "From NBA/Streett to Deterministic Parity" | 18,501 | Detailed determinization constructions (Safra trees → parity). DBA as special case. Explicit state complexity bounds. | **Good** — relevant for DBA→DPA conversion |
| **Vardi 1996** — "Automata-Theoretic Approach to LTL" | 21,667 | DBA mentioned peripherally. Focus is NBA for LTL. Büchi-Landweber reference in bibliography. | **Peripheral** |
| **Schewe 2009** — "Büchi Complementation Made Tight" | 10,312 | Complementation bounds for NBA. DBA as contrast case (complement is easy when deterministic). | **Peripheral** |
| **Kupferman & Vardi 2001** — "Weak Alternating Automata" | 16,468 | Alternation hierarchy. Weak DBA ≡ DBA for co-Büchi. | **Tangential** |
| **Baier & Katoen 2008** — *Principles of Model Checking* (12 parts) | ~480,000 | Textbook treatment of DBA limitations and constructions. Chapter 4 covers ω-automata, DBA expressiveness. | **Good** — clear textbook exposition |
| **Courcoubetis et al. 1992** — Memory-efficient verification | 8,348 | Nested DFS for emptiness checking. Not DBA-specific. | **Not relevant** |
| **Schwoon & Esparza 2005** — On-the-fly algorithms | 11,342 | Verification algorithms. Not DBA-specific. | **Not relevant** |

### 3.2 Available in specs/literature/

No DBA-specific entries. The existing temporal logic sources (Burgess, Gabbay, Reynolds) are
not relevant to DBA constructions.

### 3.3 Assessment for `--lit` Flag

**Adequate for research and basic implementation**: Thomas 1997 alone provides the theoretical
foundation. Piterman 2007 adds determinization detail. Baier & Katoen provides textbook backup.

**Gap**: No dedicated DBA-focused source. The standard references that would strengthen
coverage are:

### 3.4 Recommended Additional Sources

| Source | Why | Priority |
|--------|-----|----------|
| **Löding 2001** — "Efficient minimization of deterministic weak ω-automata" (IPL) | DBA minimization, canonical form, decidability of DBA-recognizability | High — directly relevant to §2.3 |
| **Landweber 1969** — "Decision problems for ω-automata" (Math. Systems Theory) | Original DBA characterization: DBA = Gδ ∩ ω-regular. Foundation for §2.2 | Medium — Thomas 1997 covers the result |
| **Calbrix, Nivat & Podelski 1993** — "Ultimately periodic words of rational ω-languages" | Characterization via ultimately periodic words, relevant to DBA decidability | Low |
| **Krishnan, Puri & Brayton 1995** — "Deterministic ω-automata vis-a-vis deterministic Büchi automata" (Tech report) | DBA closure properties, systematic treatment | Low |
| **Safra 1988** — "On the complexity of ω-automata" (FOCS) | Original Safra construction. Already covered by Thomas 1997 and Piterman 2007 in the Literature. | Low — already covered indirectly |

**Recommendation**: Thomas 1997 is sufficient for implementation. If pursuing the Landweber
characterization (§2.2), having Landweber 1969 would be ideal but Thomas 1997 §5 covers the
essential content. Löding 2001 is the only source that would substantially expand what can be
formalized beyond the existing literature.

## 4. Recommended Scope for Task 243

Given the existing infrastructure, the task should focus on results that complement the
already-proved theorems. Recommended phased approach:

### Phase 1: DBA Non-Closure Results (Small, Clean)

- `DA.Buchi.not_closed_complement`: DBA languages are not closed under complement.
  Proof: `not_da_buchi` already provides the witness; wrap as a clean statement.
- `DA.Buchi.not_closed_union`: DBA languages are not closed under union.
  Proof: complement of (eventually zero) = (infinitely many a's), which IS DBA-recognizable;
  if DBA were closed under union, then complement(L) = Σω \ L would be DBA (since DBA is
  closed under intersection via product), contradicting `not_da_buchi`.
- Target: `Cslib/Computability/Automata/DA/BuchiClosure.lean`, ~100–150 lines.

### Phase 2: DBA Intersection (Product Construction)

- `DA.Buchi.inter`: product DBA for intersection, with correctness proof.
- The construction uses `DA.prod` (already exists) with a 3-state acceptance tracking counter.
- Target: `Cslib/Computability/Automata/DA/BuchiInter.lean`, ~150–200 lines.

### Phase 3: DBA Characterization (Landweber)

- `DA.Buchi.language_iff_omegaLim`: an ω-regular language L is DBA-recognizable iff
  L = (L↓fin)↗ω where L↓fin is the set of finite prefixes that can be extended to an
  accepting run.
- Builds on `buchi_eq_finAcc_omegaLim`.
- Target: `Cslib/Computability/Automata/DA/BuchiChar.lean`, ~200–300 lines.
- This is the most substantial and valuable contribution.

### Phase 4: DBA → DMA / DBA → DPA Conversions

- Trivial conversions linking DBA acceptance to Muller and parity acceptance.
- Better suited as part of task 252 (acceptance conditions zoo).
- Defer unless task 252 is not planned.

### Estimated Total Scope

Phases 1–3: ~450–650 lines of new Lean code across 2–3 new files.

## 5. Key Definitions and Theorems to Formalize

```
-- Phase 1: Non-closure
theorem DA.Buchi.not_closed_complement :
  ∃ (Symbol : Type) (L : ωLanguage Symbol),
    (∃ S (da : DA.Buchi S Symbol), language da = L) ∧
    ¬ ∃ S (da : DA.Buchi S Symbol), language da = Lᶜ

theorem DA.Buchi.not_closed_union :
  ∃ (Symbol : Type) (L₁ L₂ : ωLanguage Symbol),
    (∃ S (da : DA.Buchi S Symbol), language da = L₁) ∧
    (∃ S (da : DA.Buchi S Symbol), language da = L₂) ∧
    ¬ ∃ S (da : DA.Buchi S Symbol), language da = L₁ ⊔ L₂

-- Phase 2: Intersection
def DA.Buchi.inter (a₁ : DA.Buchi S₁ Σ) (a₂ : DA.Buchi S₂ Σ) :
    DA.Buchi (S₁ × S₂ × Fin 3) Σ

theorem DA.Buchi.inter_language_eq :
    language (a₁.inter a₂) = language a₁ ⊓ language a₂

-- Phase 3: Characterization
theorem DA.Buchi.language_eq_omegaLim (da : DA.Buchi S Σ) :
    language da = (language (DA.FinAcc.mk da.toDA da.accept))↗ω
-- (This is already `buchi_eq_finAcc_omegaLim` — build characterization on top)
```

## 6. Relationship to Other Tasks

| Task | Relationship |
|------|-------------|
| 241 (McNaughton's theorem) | McNaughton = DMA ↔ NBA. DBA → DMA conversion (Phase 4) is a prerequisite step. |
| 245 (Formula Encodable/Countable) | Independent. |
| 248 (NBA emptiness) | Completed. DBA emptiness is simpler (reachability in deterministic graph). |
| 250 (NBA complementation) | NBA complement uses determinization. DBA complement is trivial (swap accept). |
| 252 (Acceptance conditions zoo) | DBA → DMA / DBA → DPA conversions should live in task 252. |

## 7. Conclusion

The existing CSLib infrastructure already covers the DBA definition, DBA → NBA embedding,
DBA language ⊂ ω-regular, and the DBA expressiveness limitation. The available literature
(Thomas 1997 + Piterman 2007 + Baier & Katoen 2008) is **adequate for `--lit` usage**.

The recommended scope focuses on: (1) non-closure results as clean corollaries of existing
theorems, (2) direct DBA intersection via product construction, and (3) the Landweber
characterization connecting DBA-recognizability to ω-limits. The Löding 2001 paper would
be the single most valuable addition to the literature if the Landweber characterization
or DBA minimization is pursued.
