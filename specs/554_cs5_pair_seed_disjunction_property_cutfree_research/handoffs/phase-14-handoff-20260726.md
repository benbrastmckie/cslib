# Phase 14 Handoff: Nested Derivations of the `CS5` Axioms

**Status**: blocked. `cut` and `NestedProof.CutFree` are landed, verified, and committed (a real,
independent contribution). The phase's main goal -- deriving all 17 `CS5ModalAxiom` constructors
as `NestedProof` witnesses -- is blocked on a genuine, Lean-verified structural obstruction, not a
skill/analysis gap. This handoff documents the exact obstruction with reproducible Lean evidence
and recommends how to proceed.

## Immediate Next Action

Before dispatching a follow-up on this phase, a **planning decision** is needed: either (a)
insert Phase 19's weakening/exchange admissibility work (or an equivalent) *before* this phase in
the dependency order, since the propositional axioms appear to need it; or (b) have a second pass
re-examine whether `Proposition 3.1`'s "straightforward induction" (source's own words) has a
formalization this session missed -- the source's confidence that this is easy is in tension with
the wall found here, and it is worth a second pair of eyes before concluding the wall is
permanent. Do **not** re-attempt the exact same `OutputCtx.fillFull`-uniform induction approach
without first reading "What Was Tried" below.

## Current State

`Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean` now additionally has:
- `NestedProof.cut` (eq. (3.1), page 7): `InputCtx`-shaped, mirrors `impL`'s output-pruning
  pattern exactly (`ctx.outputPruning.fillRhs (.atom A) → ctx.fillLhs (.atom A) → ctx.fillEmpty`).
- `NestedProof.CutFree`: mirrors `SeqProof.CutFree` in `LJ/Basic.lean`, `False` at `.cut`,
  conjunctive elsewhere.
- `NestedProof.height`'s `.cut` case.

Committed as `969bf2bb` ("task 554 phase 14.1: add cut rule and CutFree predicate to
NestedProof"). Scoped `lake build Cslib.Logics.Modal.Metalogic.Constructive.Nested.Rules` is
green (verified via `lake build` in this dispatch).

**No `Completeness.lean` file has been created** -- there is nothing sorry-free to put in it yet,
and creating it with 17 `sorry`s would violate the anti-analysis / strategic-sorry policy (each
of the 17 would be an *unresolved-approach* sorry, not a deliberate skeleton division point with
a known follow-up shape).

## What Was Tried

1. Read Proposition 3.1 (page 7: "the rule `id \overline{Γ{A•,A°}}` is derivable in `NCK`" by "a
   straightforward induction") and eq (3.1) (page 7: `nec`, `w`, `cut`, all "not part of the
   system but... admissible") directly from the source PDF, cross-referencing Figure 5 (page 13,
   "Proofs of the axioms d, t, b, 4, and 5").
2. Attempted to build `genId : ∀ (ctx : OutputCtx Atom) (A : Proposition Atom), NestedProof
   (ctx.fillFull (.atom A, .atom A))` (matching `id`'s own post-repair `OutputCtx.fillFull` shape)
   by induction on `A`, intending this as reusable machinery for every one of the 17 axiom
   derivations (each of which is, or reduces via `impR`/`andR`/etc. to, an application of general
   `id` to its own schema variables).
3. Hit an apparent wall at `A = ⊥`: `impR`'s premise (needed at the top level for `efq`, and
   internally for any axiom whose schema is an implication -- i.e. all 17) needs a *bare*,
   `.atom`-shaped RHS pair `(⊥•, π)` at an `OutputCtx` of length 0 or 1. The only introduction
   rule for `⊥` is `botL`, which is `InputCtx.fillLhs`-shaped.
4. **Verified directly in Lean** (not by hand) that `InputCtx.fillLhs`/`InputCtx.fillEmpty`
   *always* produce a `.box`-shaped RHS component, regardless of context length or content:

   ```lean
   theorem buildRhsChain_box_shape (l : List (NestedLhs Atom)) (Φ : NestedLhs Atom)
       (Ψ : NestedRhs Atom) :
       ∃ Φ' Ψ', buildRhsChain l (.box Φ Ψ) = .box Φ' Ψ' := by
     cases l with
     | nil => exact ⟨Φ, Ψ, rfl⟩
     | cons Γ rest => exact ⟨Γ, buildRhsChain rest (.box Φ Ψ), rfl⟩

   theorem InputCtx_fillLhs_snd_box (ctx : InputCtx Atom) (Δ : NestedLhs Atom) :
       ∃ Φ' Ψ', (ctx.fillLhs Δ).2 = .box Φ' Ψ' := by
     unfold InputCtx.fillLhs OutputCtx.fillRhs
     cases ctx.Γ' with
     | nil => exact ⟨ctx.Λ.fillLhs Δ, ctx.π, rfl⟩
     | cons Γ rest => exact buildRhsChain_box_shape rest (ctx.Λ.fillLhs Δ) ctx.π

   theorem InputCtx_fillEmpty_snd_box (ctx : InputCtx Atom) :
       ∃ Φ' Ψ', ctx.fillEmpty.2 = .box Φ' Ψ' := by
     unfold InputCtx.fillEmpty OutputCtx.fillRhs
     cases ctx.Γ' with
     | nil => exact ⟨ctx.Λ.fillEmpty, ctx.π, rfl⟩
     | cons Γ rest => exact buildRhsChain_box_shape rest ctx.Λ.fillEmpty ctx.π
   ```

   These type-check (confirmed via `lean_run_code`, not yet landed in the repo since they
   document the *problem*, not progress -- land them at the top of whatever file resolves this,
   as the formal record of the obstruction). This is a complete case analysis (`ctx.Γ' = []` vs.
   `Γ :: rest`), so it holds for **every** `InputCtx`, unconditionally.
5. Concluded from (4): `botL`, `cut`, `contract`, `andL`, `boxL`, `diaL`, `tL`, `fourL`, `bStruct`
   (and `w`, per eq (3.1)'s own `Γ{∅}/Γ{Δ•}` statement, which is the same `InputCtx.fillLhs`/
   `fillEmpty` shape) can **never** supply a bare `.atom`-shaped RHS. Only `id`, `andR`,
   `orRLeft`, `orRRight`, `impR`, `orL`, `tR` (all `OutputCtx`-shaped) can, and `id` is restricted
   to a base-type `Atom`, not an arbitrary `Proposition` (so it cannot stand in for `⊥` or any
   compound formula).
6. Checked whether a *nonempty*-length `OutputCtx` for `id` rescues anything: `id ctx a` for
   `ctx` of length ≥ 2 *does* produce a `.box`-shaped result (via `buildFullChain`'s recursive
   case), which superficially looks promising for matching `tL`'s `InputCtx`-shaped premise in
   Figure 5's own `t`-axiom derivation -- but the exact comma order produced by `id`/
   `OutputCtx.fillFull` (`.comma A ctx_head`, filled-formula first) does not match the order
   `InputCtx.fillLhs`'s own recursion produces (`.comma ctx_head A`, junk first) at the position
   this would be needed. This is a **second, independent** issue: `NestedLhs.comma` is a raw,
   non-quotiented constructor (`Syntax.lean`'s own "Comma Treatment" design note explicitly
   anticipates this: "supplied by explicit lemmas at the point of use... not landed speculatively
   ... since no downstream phase yet consumes them" -- this phase is the first consumer).
7. Considered simulating "modus ponens" via `cut` to bridge a `botL`-derived boxed fact
   (`□(⊥⊃φ)`, itself reachable) down to the bare `⊥⊃φ`, but `cut`'s own conclusion
   (`ctx.fillEmpty`) is *also* `InputCtx`-shaped (proof (4) above covers it too), so it cannot
   produce a bare `.atom` conclusion either -- cut does not rescue this.

## Key Decisions Made

1. **`cut` is landed as a genuine primitive constructor** (not proved admissible from the other
   18/19), exactly as the plan's task specified, mirroring `SeqProof.cut`/`LJProof`'s treatment.
   This was completed and is solid regardless of the rest of this phase's outcome.
2. **No `Completeness.lean` file was created.** Per the anti-analysis strategic-sorry policy, a
   `sorry` is only legitimate as a *deliberate skeleton division point* with a known follow-up,
   not a stand-in for "this approach didn't work." All 17 axiom derivations currently share the
   *same* unresolved dependency (general `id`'s `A = ⊥` case), so a file of 17 `sorry`s would not
   meet the five-condition strategic-sorry test (in particular condition 3, "documented... why it
   was deferred," and condition 2, "scoped to exactly one theorem" -- these would all share one
   root cause, better documented once, here, than duplicated 17 times).
3. **Did not add `w` (weakening) as an extra primitive constructor.** It was considered (eq (3.1)
   groups `nec`/`w`/`cut` together, and several axioms -- e.g. `implyK`, which needs to discard an
   unused hypothesis `ψ` -- appear to need it), but proof (4) above shows `w`'s own `Γ{∅}/Γ{Δ•}`
   shape is *also* `InputCtx.fillLhs`/`fillEmpty`-shaped, so adding it would **not** resolve the
   `efq`/general-`id` blocker (it is a different obstruction: `w` helps with discarding/adding
   unused hypotheses in a comma list, but does not help produce a bare `.atom`-shaped RHS headed
   by `⊥`). Adding `w` might still be necessary for `implyK` and similar axioms *once* the
   general-`id` blocker is resolved, so it remains a live candidate for a follow-up, just not a
   fix for *this* wall.

## What NOT to Try

- Do not re-attempt `genId` as a single induction on `A` uniformly targeting
  `OutputCtx.fillFull (A, A)` -- the `A = ⊥` case is a proven dead end (see (4) above), not a
  matter of trying harder tactics.
- Do not try to "shed" `botL`'s unavoidable `.box` wrapping via `boxR` -- `boxR`'s premise needs
  the LHS component to be `.empty` specifically; `botL`'s output always has `⊥` (or
  `Λ.fillLhs ⊥`) there, never `.empty`, so `boxR` never applies to a `botL`-derived term.
- Do not try to add `cut` (already landed) as the fix for the bare-`⊥`-on-LHS problem -- `cut`'s
  own conclusion shape (`ctx.fillEmpty`) is `InputCtx`-shaped and subject to the same proof (4).
- Do not assume Figure 5's own derivations are unaffected: this handoff only *positively confirms*
  that Figure 5's `t`/`4`/`b`-axiom recipes avoid needing weakening/cut/comma-swap themselves
  (visually, no `w` or `cut` step appears in Figure 5's images) -- but they still need general
  `id` for an arbitrary formula `A` (which the same `A = ⊥` wall affects), so they are **not**
  confirmed unblocked either; this was not fully re-verified after the wall was found, for lack
  of remaining budget this dispatch.

## Remaining Goals (verbatim from plan)

- [ ] Derive each of the nine propositional constructors, `k`, `kdia`, `tBox`, `tDia`, `fourBox`,
      `fourDia`, `bBox`, `bDia` as `NestedProof (ψ◦)` -- blocked, see above.
- [ ] Cross-check against §5's "Proofs of the axioms d, t, b, 4, and 5 in our system" -- not
      reached; general `id` (a prerequisite Figure 5 itself relies on) is blocked first.
- [ ] `lake build` (module-scoped, for a `Completeness.lean` that does not yet exist).

## References

- Plan: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/plans/02_cutfree-pair-conservativity.md`
  (Phase 14 section, updated with a Blocker note)
- Progress: `specs/554_cs5_pair_seed_disjunction_property_cutfree_research/progress/phase-14-progress.json`
- Code: `Cslib/Logics/Modal/Metalogic/Constructive/Nested/Rules.lean` (commit `969bf2bb`)
- Source: `~/Projects/Literature/.sources-recovered/arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics.pdf`,
  pages 7 (Proposition 3.1, eq (3.1), Figure 3), 8-9 (Figure 4, Theorem 4.1, Lemma 4.2-4.6),
  11-13 (Lemma 4.11 proof, Lemma 4.12, Figure 5)
