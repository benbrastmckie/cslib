/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

import Cslib.Init
public import Cslib.Logics.Modal.Metalogic.Constructive.CS5

/-! # `CS5` Birelational Canonical Model (Task 512 Pivot)

This module is being rebuilt as the **birelational canonical model** for `CS5` (Božić–Došen
1984 / Došen 1985 IS5 / Simpson 1994 / Alechina–Mendler–de Paiva–Ritter 2001), replacing the
abandoned doubled-atom `CS5Combined` atom-sum scaffold (task 512 plan 01, DISCARDED this phase
— see `specs/512_cs5_box_backward_atom_sum_completeness/plans/02_birelational-pivot.md`, Phase
2). The doubled-atom approach attempted to close `CS5`'s box-backward truth-lemma case via a
simultaneous-pair construction over `Atom ⊕ Atom`; five dispatches confirmed this re-enters
Pacheco's unsound negation-completeness move (`cs5Combined_seed_excludes`, never closed — see
git history for the removed content).

The birelational pivot makes the canonical relation **one-sided** (`Γ R Δ ⟺ boxInv Γ ⊆ Δ`,
Simpson's `{B | □B ∈ X} ⊆ Y`), dissolving box-backward to the plain one-sided prime lemma
(`box_refuting_theory`, `SegmentLindenbaum.lean`) — confirmed negation-completeness-free at the
Phase 1 gate
(`specs/512_cs5_box_backward_atom_sum_completeness/probes/phase1-onesided-box-backward-gate.lean`,
`cs5_box_backward_onesided`). Symmetry becomes a global ≤-mediated **incestuality** frame
condition (Marin–Morales–Straßburger 2021 Thm 7.1) instead of a per-world back-inclusion baked
into `cs5Tail` (`CS5.lean:632`).

## Status (Phase 2 of the pivot: scaffold discard)

This phase removes the `CS5Combined` doubled-atom machinery (`CS5Combined`, `cs5_axiom_relabel`,
`τL`/`τR`, `cs5Combined_necTransfer`, `cs5CombinedTail`/`cs5CombinedSeg`/`CS5CombinedSegment`/
`cs5CombinedMreach`, and every port of `CS5.lean`'s canonical-model machinery over the doubled
atom space) as dead code — none of it survives the pivot, and nothing else in `Cslib/` referenced
it (confirmed by grep before removal). `Proposition.map` — the one still-useful primitive from
plan 01 — already lives in `Cslib/Logics/Modal/Basic.lean`, not here, so no file-split action was
needed this phase.

The two general negative results the pivot's research explicitly retains stay in their original
files, untouched by this discard:
- `cs5_symmetric_tail_box_gap` (`CS5.lean:712`) — the mechanized diagnosis of why the two-sided
  `cs5Tail` back-inclusion is the box-backward wall.
- `cs5FC''_hub_forces_spoke_connectivity` (`CKExtension.lean:220`) — the general fact that plain
  symmetry + plain transitivity force hub-and-spoke collapse (irrelevant as an obstruction to the
  new incestuality-based design, but a documented fact in its own right).

The birelational frame class (one-sided `R` + incestuality condition) is added in Phase 3;
soundness, canonical verification, box-backward, and the truth lemma follow in Phases 4-7. See
the plan file for the full phase breakdown.

## References

* [D. Božić and K. Došen, *Models for Normal Intuitionistic Modal Logics*][BozicDosen1984]
* [K. Došen, *Models for Stronger Normal Intuitionistic Modal Logics*][Dosen1985]
* [A. Simpson, *The Proof Theory and Semantics of Intuitionistic Modal Logic*][Simpson1994]
* [N. Alechina, M. Mendler, V. de Paiva and E. Ritter, *Categorical and Kripke Semantics for
  Constructive S4 Modal Logic*][AlechinaMendlerdePaivaRitter2001]
* [S. Marin, D. Morales and L. Straßburger, *A Fully Labelled Proof System for Intuitionistic
  Modal Logics*][MarinMoralesStrassburger2021]
* [L. Pacheco, *Collapsing Constructive and Intuitionistic Modal Logics*][Pacheco2024]
-/

@[expose] public section

namespace Cslib.Logic.Modal

open Cslib.Logic

universe u

variable {Atom : Type u}

end Cslib.Logic.Modal

end
