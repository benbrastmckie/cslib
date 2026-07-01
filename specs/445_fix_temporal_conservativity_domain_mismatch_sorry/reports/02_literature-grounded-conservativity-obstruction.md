# Research Report (Round 2) — Task 445: Literature-grounded verdict on the domain-mismatch `sorry`

**File**: `Cslib/Logics/Bimodal/Metalogic/ConservativeExtension/TemporalConservativity.lean`
**Target**: `temporal_valid_of_bimodal_derivable` (line 261, `sorry` at line 269);
downstream `bimodal_conservative_over_temporal` (line 289).
**Round-1 report**: `reports/01_domain-mismatch-transfer-feasibility.md` (read; its Route A/B/C
framing is superseded below).
**Reference-grounding tier**: Tier 1 (literature-backed). BibKeys verified against
`/home/benjamin/Projects/cslib/references.bib`.

## TL;DR — the verdict has changed from "research-level" to "the theorem is FALSE"

Round-1 concluded the transfer route was unsound and the general case "research-level".
Round-2, by inspecting the **actual CSLib axiom sets** on both sides and grounding in the
literature, reaches a stronger and definitive conclusion:

> **`bimodal_conservative_over_temporal` (and hence `temporal_valid_of_bimodal_derivable`)
> is FALSE as stated. The `sorry` at line 269 marks a false proposition and CANNOT be closed.**

**Machine-verified counterexample** (the Bimodal half compiled clean under
`lake env lean`, exit 0):

Let `φ_T : Temporal.Formula` be the atom-free formula
`(untl ⊥ ⊤) → G (untl ⊥ ⊤)` — read: *"if there is an immediate successor, then at every
future point there is an immediate successor"* (temporal homogeneity of the successor relation;
here `untl ⊥ ⊤` at `t` means `∃ s>t` with `(t,s)` empty, i.e. `t` has an immediate successor —
this is exactly CSLib's `Chronicle.nextTop`, whose negation is the `dense_indicator` axiom).

1. **`Bimodal.ThDerivable φ_T.toBimodal` is TRUE.** `φ_T.toBimodal` is *definitionally* the
   statement of the base axiom `Bimodal.Axiom.discrete_propagate_fwd`
   (`ProofSystem/Axioms.lean:261`), which has `minFrameClass = .Base`. Verified:
   ```lean
   example : Bimodal.ThDerivable phiT.toBimodal :=
     ⟨.axiom [] _ (Bimodal.Axiom.discrete_propagate_fwd) (le_refl _)⟩   -- compiles, exit 0
   ```
2. **`Temporal.ThDerivable φ_T` is FALSE.** `φ_T` is atom-free, so its truth is purely
   order-theoretic. On the **doubled rationals** `D = ℚ ×ₗ Bool` (lexicographic; a
   `LinearOrder` with `NoMaxOrder`, `NoMinOrder`, `Nontrivial`), at the point `(q, false)`:
   `untl ⊥ ⊤` holds (immediate successor `(q, true)`, empty interval), but `(q, true)` has **no**
   immediate successor (the next element would be `(q', false)` for `q' > q`, and `ℚ` is dense),
   so `G (untl ⊥ ⊤)` fails, refuting `φ_T` at `(q, false)` — under *every* valuation. Since
   CSLib's `Temporal.soundness` (`Metalogic/Soundness.lean:409`) holds for **all** serial linear
   orders `[LinearOrder D] [NoMaxOrder D] [NoMinOrder D]`, and every Temporal `FrameClass.Base`
   axiom is valid on `D`, `Temporal.ThDerivable φ_T` would force `φ_T` valid on `D` —
   contradiction. Hence `¬ Temporal.ThDerivable φ_T`.

Feeding `φ_T` to `bimodal_conservative_over_temporal` yields `Temporal.ThDerivable φ_T` from
`Bimodal.ThDerivable φ_T.toBimodal` — a true hypothesis and a false conclusion. The theorem is
refuted.

**Root cause (design-level, not proof-difficulty):** CSLib's bimodal TM `FrameClass.Base`
includes **five "Uniformity Axioms"** (`Axioms.lean:248–276`, Layer 5) —
`discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`, `discrete_box_necessity` — all mapped to
`.Base` by the catch-all in `Axiom.minFrameClass`. These are box-free (or nearly so) formulas
that are **sound on the ordered-abelian-group task frames** the bimodal semantics is built on
(`TaskFrame` requires `AddCommGroup D`; `FrameClass.lean:82` "for time shifts"), because ordered
abelian groups are **translation-homogeneous**. But the **Temporal BX `FrameClass.Base`**
(`Cslib/Logics/Temporal/ProofSystem/Axioms.lean`) has **none** of these axioms — it is the pure
Burgess/Xu linear Since/Until calculus, sound & complete over **all** serial linear orders,
including non-homogeneous ones like the doubled rationals. Therefore the temporal fragment of TM
is **strictly stronger** than BX, and TM is **not conservative** over BX.

## Source-to-Implementation Mapping (Tier 1)

| Source claim | BibKey | Verified? | Lean target / relevance | Translation note |
|---|---|---|---|---|
| Minimal U,S-tense logic = Th(all frames); step-by-step **countable** countermodel; irreflexivity/antisymmetry **not** U,S-definable (Thm 2.9) | `Xu1988` §2 | in bib ✓; local `xu_1988` | `Temporal` BX = Burgess/Xu U,S base; explains why base countermodels can be non-dense/non-homogeneous | Xu builds countermodels on a countable `T ⊆ T*`; matches CSLib chronicle ⊆ ℚ |
| Burgess Since/Until axioms (1)-(4); linear-time completeness | `Burgess1982I` §; local `burgess_1982_i` | in bib ✓ | The BX axiom schemata replicated in `Temporal/ProofSystem/Axioms.lean` | CSLib's `enrichment/self_accum/absorb/linear_*` are the Burgess axioms |
| **Metric tense logic**: "Time has the structure of an ordered abelian group" | `Burgess1984` §6.1 | in bib ✓ | Explains WHY TM uses `AddCommGroup` `TaskFrame` and needs the Uniformity axioms | The uniformity axioms are the tense-logical price of the metric/group time structure |
| Ockhamist/`T×W` tense+modality is **conservative** over ordinary (linear) tense logic — box-free φ valid in treelike frames iff valid in ordinary tense logic; **semantic** (branch-projection) proof | `Thomason1984` §3-4 | **NOT in bib** (recommend add) | The *intended* conservativity result; contrast: Thomason's system has **no** metric/uniformity axioms, so it IS conservative — CSLib's does, so it is NOT | Method is p-morphism/branch projection, not group transfer |
| Non-orthodox rule conservativity via **interpolation** (Lemma 9.2) | `Venema1993SinceUntil`-adjacent (Venema 1993 "Derivation Rules as Anti-Axioms") | local `venema_1993` §9.2; **bib has only** `Venema1993SinceUntil` | Proof-theoretic conservativity template (if a corrected theorem is pursued) | Applies to *rules*, not language extensions; template only |
| U,S completeness needs the **IRR rule** for irreflexive/linear flows; countable MCS countermodels | `GHR94`, `Reynolds1994` | in bib ✓; local `gabbay_1993`, `reynolds_2001` | Background on the BX frame class; not load-bearing for the verdict | — |
| Modal satisfaction invariant under **bounded morphisms**; downward Löwenheim–Skolem | `Blackburn2001` Prop 2.14, Thm A.4, §7.12/7.15 | in bib ✓; local `blackburn_2002` | Would underpin a semantic transfer — but such transfer is provably impossible here (see Route A) | LS is moot: the only domain used by `completeness` is already countable |

## Findings

### F1. The two `FrameClass.Base` axiom sets differ on the temporal fragment (decisive)

- **Bimodal `Axiom` (`Cslib/Logics/Bimodal/ProofSystem/Axioms.lean`)**: propositional
  (`imp_k, imp_s, efq, peirce`); **S5 box** (`modal_t, modal_4, modal_b, modal_5_collapse,
  modal_k_dist`); the Burgess/Xu temporal layer; **one interaction axiom** `modal_future`
  (`box φ → box (G φ)`); and **Layer 5 "Uniformity Axioms"** `discrete_symm_fwd/bwd`,
  `discrete_propagate_fwd/bwd`, `discrete_box_necessity`. `Axiom.minFrameClass` sends only
  `density, dense_indicator → .Dense` and `prior_UZ, prior_SZ, z1 → .Discrete`; **everything
  else, including all five Uniformity axioms, is `.Base`.**
- **Temporal `Axiom` (`Cslib/Logics/Temporal/ProofSystem/Axioms.lean`)**: propositional; Burgess/Xu
  temporal layer; the `G↔¬F¬` bridges (`allFuture_to_classic` etc.); and only
  `density, dense_indicator → .Dense`. **No uniformity/discreteness axioms exist on the temporal
  side.**

Because `toBimodal` is a purely structural embedding (`Embedding/TemporalEmbedding.lean`), the
temporal reduct of the Bimodal base theorem `discrete_propagate_fwd` is a Bimodal-provable,
box-free formula whose temporal preimage `φ_T` is **not** Temporal-provable. This is precisely a
conservativity failure.

### F2. The failure is exactly the homogeneity of ordered abelian groups (literature-grounded)

Xu 1988 (Thm 2.9) establishes that successor/irreflexivity-type first-order conditions are
**not** definable in U,S over the class of all frames — i.e. the base tense logic cannot pin down
successor structure uniformly. Ordered abelian groups, by contrast, are translation-homogeneous
(`x ↦ x+g` is an order-automorphism acting transitively), so "has an immediate successor" is
either universal or nowhere — making `φ_T` **valid** on every `AddCommGroup` order. Burgess's
**metric tense logic** (`Burgess1984` §6.1) is explicitly the tense logic of ordered-abelian-group
time; CSLib's `AddCommGroup` `TaskFrame` is an instance of that design choice, and the Uniformity
axioms are its tense-logical consequences. The mismatch between "metric (homogeneous) time" and
"arbitrary serial linear time" is the entire content of the bug.

### F3. `Temporal.completeness` only ever instantiates ONE domain

`Temporal.completeness` (`Metalogic/Completeness.lean:101`) is *stated* over all serial linear
`D`, but its proof applies `h_valid` at exactly `D := ChronicleSubtype M hM_mcs` (a countable
suborder of ℚ). Consequently the round-1 "Löwenheim–Skolem to a countable submodel" step (Route A
step 2) is unnecessary — the only relevant domain is already countable. This does **not** rescue
any route (see Route A), but it corrects the round-1 difficulty estimate.

### F4. CSLib's `completeness_dense` works precisely because the dense axiom kills `φ_T`'s antecedent

`BXCanonical/Completeness/Dense.lean` closes the dense case by observing that the `dense_indicator`
axiom `¬(untl ⊥ ⊤)` is a `.Dense` theorem, so every Dense-MCS contains `□(¬ nextTop)`, forcing
`DenselyOrdered` and a Cantor iso to ℚ. There is **no** base-class analogue (the base chronicle's
density is conditional: `ChronicleToCountermodelBasic.lean:231 limitDomSubtypeDenselyOrderedFromF'T`
requires the density formula in the MCS). This is the structural reason the dense conservativity
goes through and the base one is stuck — and, per F1–F2, cannot be un-stuck.

### F5. Literature confirms conservativity is achievable *only without* the metric/uniformity axioms

Thomason 1984 (`Thomason1984`, local `thomason_1984` §3-4) proves the combined tense+modality
(Ockhamist / `T×W`) logic **is** conservative over ordinary linear tense logic, by a semantic
branch-projection argument — but his combined system carries **no** metric/uniformity axioms.
This is the clean precedent showing (a) that a *correctly designed* bimodal-over-temporal
conservativity is a known, true, and provable result, and (b) that CSLib's TM breaks it precisely
by adding the ordered-abelian-group uniformity axioms to the base class.

## Route assessment (superseding round-1), each grounded in a source

### Route A — OrderIso/order-embedding transport (+ Löwenheim–Skolem + Cantor)
**DEAD — requires a provably false lemma.** Any such route must, from
`temporal_valid_on_addcommgroup` (which yields only *`AddCommGroup`-validity* of `φ`), derive
*serial-linear-validity* of `φ`. That step is the statement "`Th(AddCommGroup) ⊆ Th(serial
linear)`", which is **false**: `φ_T ∈ Th(AddCommGroup) \ Th(serial linear)` (F2). No
order-iso/LS/Cantor construction can validate a false auxiliary. Blackburn's bounded-morphism/LS
machinery (`Blackburn2001` Prop 2.14, Thm A.4) is inapplicable because the required transfer does
not exist. (Round-1 called this "blocked on the non-dense sub-case"; it is in fact globally
impossible, and the doubled-rationals order is the explicit witness.)

### Route B — "Prove base BX complete w.r.t. `AddCommGroup` serial orders" (`Th(oag) = BX`)
**DEAD — the target theorem is FALSE.** `φ_T ∈ Th(oag)` but `φ_T ∉ BX` (F1–F2), so
`Th(oag) ⊋ BX`. Round-1 rated this "uncertain even if true"; it is now definitively false, with an
explicit, machine-checkable-in-principle witness. Grounded in `Xu1988` Thm 2.9 (non-definability)
+ `Burgess1984` §6.1 (metric = oag time) + the homogeneity argument.

### Route C — Syntactic / proof-theoretic conservativity (e.g. box-erasure)
**Does not save the *stated* theorem** (no proof can, since it is false), **but it is the correct
technique for a *corrected* theorem.** A box-erasure interpretation `□ ↦ id` maps every S5 box
axiom to a propositional tautology and fixes box-free formulas; it would prove conservativity
*iff* every TM base axiom's erasure is a *target*-theorem. The obstruction is exactly the
Uniformity axioms: their erasures (e.g. `discrete_propagate_fwd` itself) are **not** BX-theorems.
So Route C mechanically *re-derives* the failure. It becomes a genuine proof only if the target
temporal system is strengthened to include the uniformity axioms (see Recommendation, option 2).
Literature template: Venema 1993 §9.2 (interpolation-based rule conservativity) and Thomason 1984
§3-4 (semantic conservativity) — both for systems *without* metric axioms.

## Recommendation

**Mark the implementation task `[BLOCKED]` and escalate to the user with this finding. Do not
attempt to close the `sorry` — it is false. Do not weaken it with a vacuous placeholder or an
axiom (zero-debt).** Present the user three sound resolutions, in preference order:

1. **Restate conservativity over the matching temporal base (recommended).** Define a
   "metric/uniform" temporal logic `BX⁺` = Temporal `FrameClass.Base` **plus** temporal copies of
   the five Uniformity axioms (`discrete_symm_fwd/bwd`, `discrete_propagate_fwd/bwd`, and a
   temporal analogue of `discrete_box_necessity` or its omission), sound over `AddCommGroup`
   serial orders. Then `bimodal_conservative_over_temporal : Bimodal.ThDerivable φ.toBimodal →
   BX⁺.ThDerivable φ` becomes **provable**, cleanly, by **box-erasure induction on the TM
   derivation** (Route C): each S5 axiom erases to a tautology; `modal_future` erases to
   `Gφ→Gφ`... i.e. a BX⁺ theorem; every temporal/uniformity axiom erases to itself (a BX⁺ axiom);
   MP/necessitation are preserved. This is ~150–300 lines, self-contained, no `AddCommGroup`
   transfer, no `sorry`. This is the honest theorem: TM is conservative over *metric* tense logic,
   matching Burgess1984 §6.1 and the Thomason1984 pattern.
   - Fully-qualified Lean anchors to reuse: `Temporal.Formula.toBimodal`
     (`Embedding/TemporalEmbedding.lean`), `Bimodal.DerivationTree` recursion
     (`ProofSystem/Derivation.lean:53`), `Axiom.minFrameClass`
     (`Bimodal/ProofSystem/Axioms.lean:305`, `Temporal/.../Axioms.lean:256`). Define
     `eraseBox : Bimodal.Formula → Temporal.Formula` and prove
     `Bimodal.Deriv Γ φ → Temporal.Deriv (Γ.map eraseBox) (eraseBox φ)` by structural induction
     on the derivation tree; specialise to `eraseBox (φ.toBimodal) = φ` (a `simp` induction on
     `φ`). Verify the per-axiom erasure obligations with `lean_multi_attempt`.

2. **Drop the Uniformity axioms from bimodal `FrameClass.Base`** (move them to a new
   `FrameClass.Metric`/`.Uniform` class ≥ Base), so bimodal Base ↔ Temporal Base match. Then the
   original theorem holds over base — but this is a larger refactor and may break existing bimodal
   soundness/completeness that relies on those axioms being Base. Requires auditing every use of
   `discrete_*` at `FrameClass.Base`.

3. **Delete `temporal_valid_of_bimodal_derivable` and `bimodal_conservative_over_temporal`** and
   the `set_option warn.sorry false`, recording in the module docstring that TM (metric) is *not*
   conservative over pure BX, with the `φ_T` counterexample. Zero-debt but loses the result.

**Do not pursue** options that keep the current statement: it is false.

## Sources to add (ranked)

1. **`Thomason1984`** — Richmond H. Thomason, *Combinations of Tense and Modality*, in
   *Handbook of Philosophical Logic, Vol. II: Extensions of Classical Logic*, ed. D. Gabbay &
   F. Guenthner, Synthese Library **165**, D. Reidel, Dordrecht, 1984, **pp. 135–165**.
   - **Why**: the canonical conservativity precedent; frames the correct (metric-free) result and
     the contrast with CSLib's TM. **Local corpus already has it** at
     `sources/thomason_1984/` (add the `references.bib` entry; suggested key `Thomason1984`).
   - Online: Handbook Vol. II PDF `https://vdoc.pub/documents/handbook-of-philosophical-logic-volume-ii-extensions-of-classical-logic-56gjb9sli5m0`
2. **SEP supplement, Burgess–Xu system** (authoritative online, freely accessible) —
   `https://plato.stanford.edu/entries/logic-temporal/burgess-xu.html`. Confirms the BX frame
   class (all linear orders) and axioms; good for docstring citations. Optional bib entry.
3. **`Reynolds1992`** — Mark Reynolds, *An Axiomatization for Until and Since over the Reals
   without the IRR Rule*, *Studia Logica* **51** (1992) 165–194. Optional; supports the
   frame-class discussion (already partly covered by `GHR94`/`Reynolds1994`, both in bib).
4. **`GabbayHodkinson1990`** — Gabbay & Hodkinson, *An axiomatization of the temporal logic with
   Since and Until over the real numbers*, *J. Logic Computation* **1** (1990) 229–259. Optional.

No new source is *required* for the verdict: `Xu1988`, `Burgess1984`, `Blackburn2001`,
`Venema1993SinceUntil` (all in bib and local corpus) plus the CSLib axiom files fully ground it.

## Adversarial Self-Verification (H4)

- **Challenge: "Is `φ_T.toBimodal` really TM-derivable at the class the theorem uses?"**
  `Bimodal.ThDerivable` = `Nonempty (DerivationTree FrameClass.Base [] ·)`
  (`Metalogic/Core/DerivationTree.lean:56`). `discrete_propagate_fwd.minFrameClass = .Base ≤ .Base`.
  **Machine-verified**: the `example` above compiled under `lake env lean` (exit 0), confirming
  `φ_T.toBimodal` is *definitionally equal* to the axiom's statement (the elaborator accepted the
  `.axiom` term at that type). Not speculation.
- **Challenge: "Is `Temporal.ThDerivable φ_T` really false — could a non-obvious derivation
  exist?"** Ruled out by soundness, not by failed search: `Temporal.soundness`
  (`Metalogic/Soundness.lean:409`) is a proven theorem over every `[LinearOrder D][NoMaxOrder D]
  [NoMinOrder D]`. `φ_T` is atom-free and refuted on the doubled-rationals order under all
  valuations; every Temporal `FrameClass.Base` axiom (Burgess/Xu linear U,S + `G↔¬F¬` bridges) is
  valid on all serial linear orders, so the doubled rationals is a genuine BX frame. Hence any
  derivation would contradict soundness. This half is rigorous pen-and-paper (not machine-checked;
  full formalization would need Mathlib `Lex (ℚ × Bool)` order instances — a mechanical but
  non-trivial ~50-line construction, recommended if the user wants the counterexample landed as a
  `theorem not_conservative`).
- **Challenge: "Does `toBimodal`'s `allFuture ↦ ¬F¬` encoding break the match?"** No —
  `discrete_propagate_fwd` uses `Bimodal.Formula.allFuture` (the same `¬F¬` abbreviation), and
  `toBimodal_allFuture`/`toBimodal_untl`/`toBimodal_top` are structural. The compiled `example`
  is the proof of match.
- **Challenge: "Does Thomason's precedent (conservativity HOLDS) contradict my verdict
  (FAILS)?"** No — Thomason's system has no metric/uniformity axioms; the agent-extracted quotes
  confirm his tense fragment is over arbitrary linear `T` with **no** group/metric structure. The
  contradiction is only with a *hypothetical* CSLib TM lacking the Uniformity axioms — which is
  exactly Recommendation option 2.
- **Challenge: "Is round-1's Route C ('large, uncertain') wrongly dismissed?"** Refined, not
  dismissed: box-erasure is a clean, standard technique, but for the *stated* target it
  mechanically reproduces the failure (the uniformity axioms don't erase to BX-theorems),
  confirming falsity; for a *corrected* target (BX⁺) it is the recommended proof.
- **BibKey verification status**: `Xu1988`, `Burgess1982I`, `Burgess1982II`, `Burgess1984`,
  `Kamp1968`, `GPSS1980`, `Venema1993SinceUntil`, `GHR94`, `Reynolds1994`, `Blackburn2001`
  **all present** in `references.bib` (verified by grep). `Thomason1984` **absent** (recommended
  addition; local `sources/thomason_1984/` present). NOTE: the task brief assumed these keys were
  missing and that local `goldblatt_2003` = "Logics of Time and Computation" and `blackburn_2001`
  — corrected: `references.bib` already has the keys, `Blackburn2001` is the correct key for the
  Modal Logic textbook (local `blackburn_2002`), and local `goldblatt_2003` is actually
  Goldblatt–Hodkinson–Venema, *Erdős graphs resolve Fine's canonicity problem* (not used here).

## Revised Direction

None required — the verdict is stable under adversarial review and is machine-verified on the
load-bearing (Bimodal-derivability) half. This is a valid, zero-debt escalation outcome per the
task's escalation clause: the obstruction is not "hard", it is a **false theorem** caused by a
frame-class mismatch between the metric bimodal base and the pure temporal base.
