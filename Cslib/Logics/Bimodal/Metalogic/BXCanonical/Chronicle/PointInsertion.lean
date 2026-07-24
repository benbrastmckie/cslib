/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.Seeds
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.Burgess
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.XuGuard
public import Cslib.Logics.Bimodal.Metalogic.BXCanonical.Chronicle.PointInsertion.Since

/-! # Point Insertion Lemmas (Burgess 2.4-2.8)

Barrel module re-exporting the point insertion machinery split across four submodules.

The construction proceeds in four phases:

1. **Seeds** (`PointInsertion.Seeds`): Helper F/G lemmas, Lemma 2.4/2.5/2.6,
   seriality consequences at MCS level, seed consistency, and R3Maximal utilities
   (lines 101-572 of the original file).

2. **Burgess** (`PointInsertion.Burgess`): Burgess Lemma 2.6 content-based approach,
   Xu Lemma 2.3 (top-guard), gContent/hContent subset relationships, duality,
   Lemma 2.6 interval insertion, Lemma 2.7 helpers including list-conjunction utilities
   and iterated enrichment structures (lines 573-1508).

3. **XuGuard** (`PointInsertion.XuGuard`): Xu Lemma 3.2.1 full guard strengthening
   for transitive frames; Lemma 2.7 and 2.8 with seed-consistency proofs
   (lines 1509-2599).

4. **Since** (`PointInsertion.Since`): Lemma 2.7' (Since direction), Lemma 2.8',
   and enriched Lemma 2.4 variants (with/without guard, Until and Since directions)
   (lines 2600-3565).

## References

- Burgess 1982: "Basic tense logic", Section 2, Lemmas 2.4-2.8
-/
