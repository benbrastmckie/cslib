/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Seeds
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Burgess
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Splitting
public import Cslib.Logics.Temporal.Metalogic.Chronicle.PointInsertion.Since

/-!
# Point Insertion Lemmas (Burgess 2.4-2.8)

Barrel module re-exporting the point insertion machinery split across four submodules.

The construction proceeds in four phases:

1. **Seeds** (`PointInsertion.Seeds`): F/G helper lemmas, Lemma 2.4/2.5/2.6,
   MCS-level axiom helpers, seriality, DCS neg insert, and R3Maximal/BurgessR3Maximal
   properties (lines 52-519 of the original file).

2. **Burgess** (`PointInsertion.Burgess`): gContent ⊆ B from BurgessR3Maximal,
   Xu Lemma 2.3, derivation monotonicity, BX13/BX13', F/P monotonicity,
   Xu Lemma 3.2.1, duality, Lemma 2.6 interval insertion, and
   propositional/list/guard helpers (lines 520-1345 of the original file).

3. **Splitting** (`PointInsertion.Splitting`): Iterated BX13 enrichment structures,
   Lemma 2.7 Until-formula splitting, and Lemma 2.8 variant
   (lines 1346-2069 of the original file).

4. **Since** (`PointInsertion.Since`): Lemma 2.4 with guard (enriched version),
   Since-direction mirrors of Lemma 2.7/2.8, and Lemma 2.4 Since with guard
   (lines 2070-2730 of the original file).

## References

* Ported from Cslib/Logics/Bimodal/Metalogic/BXCanonical/Chronicle/PointInsertion.lean
* [J. Burgess, *Axioms for Tense Logic II: Time Periods*][Burgess1982II]
-/
