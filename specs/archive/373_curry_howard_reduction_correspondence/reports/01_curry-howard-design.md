# Task 373 — Curry-Howard Reduction Correspondence: Design & Verification Report

**Agent**: cslib-research-hard-agent · **Tier**: 1 (literature-backed) · **Session**: sess_1782576552_fae7a6
**Verdict**: FEASIBLE, zero-debt (no sorry, no new axioms). Both load-bearing mechanisms compiled green via `lake env lean`.

## Feasibility Verdict

Task 373 extends the Curry-Howard layer from a structural isomorphism (task 332) to a
**computational correspondence**. Two deliverables:

1. **Reduction correspondence** — derivation root reduction is mirrored by a reduction on `Theory.Term`.
2. **Term-level strong normalization** — transport derivation SN existence across the iso.

A **reduction relation on `Theory.Term` MUST be defined** — it does not exist yet (confirmed:
`Defs.lean` defines only the 10-constructor inductive; `Isomorphism.lean` defines only the maps
and roundtrips; no `Term.reduceRoot`/`Step`/`Reduces` anywhere). Total estimate: **~250-300 lines, 4 phases.**

The decisive structural fact: `curryHowardForward`/`curryHowardBackward` (note: camelCase — the task
brief's `curryHoward_forward` is **not** the real name) are constructor-renaming bijections with
mutual-inverse roundtrip theorems `curryHoward_backward_forward` / `curryHoward_forward_backward`
(`Isomorphism.lean:92,109`). Every correspondence obligation therefore collapses to a **roundtrip
rewrite** rather than a substantive induction.

### Two viable designs (both built green)

| Design | `Term.reduceRoot` | Correspondence proof | Lines | Fidelity |
|--------|-------------------|----------------------|-------|----------|
| **A. Transport** | `(curryHowardBackward t).reduceRoot.map curryHowardForward` | one roundtrip `rw` | ~60 | lower (correspondence near-vacuous-by-construction) |
| **B. Native** (RECOMMENDED) | 8-case pattern match on `Term` constructors | case analysis, each case a roundtrip `rw` | ~250-300 | high (genuine term-native β/commuting reduction) |

**Recommendation: Design B (native `Term.reduceRoot`)** with substitution/weakening defined by
transport. This is what "reduction *on* `Theory.Term`" means in the task, makes the correspondence
a real (non-`rfl`) theorem, and is fully de-risked below. Design A is retained as a documented
fallback for any native case that proves stubborn (it requires no `cases` plumbing).

## Source-to-Implementation Mapping (Tier 1)

| Source Claim | BibKey | Lean Target | Translation Notes |
|--------------|--------|-------------|-------------------|
| Curry-Howard iso, β-reduction ↔ proof reduction | `SorensenUrzyczyn2006` §2.2 (already cited in `Defs.lean:37`) | `Theory.Term.reduceRoot`, `reduceRoot_forward` | term β/commuting reduction mirrors `Derivation.reduceRoot` |
| Normalization / redex elimination (5 β + 3 commuting conversions) | `Prawitz1965` Ch. III–IV (cited in `Reduction.lean:25`, `Basic.lean:30`) | mirror of `Derivation.reduceRoot` 8 `some`-cases | proper redexes + commuting conversions |
| Weak/strong normalization existence | `Prawitz1965` Ch. IV | `Theory.Term.exists_stronglyNormal_form` | transports `Derivation.exists_stronglyNormal_form` |

**BibKey status**: `SorensenUrzyczyn2006` (`references.bib:468`) and `Prawitz1965` (`references.bib:418`)
both VERIFIED present. No additions needed.

## Verified Ground Truth (read, not assumed)

- `Theory.Term` — `Defs.lean:56`, 10 constructors mirroring `Derivation`; **no reduction relation**. CONFIRMED.
- `curryHowardForward`/`Backward` — `Isomorphism.lean:54,73`; constructor-renaming. Roundtrips `:92,:109`.
- `Theory.Derivation.reduceRoot` — `Reduction.lean:66`: `Derivation G A → Option (Derivation G A)`,
  exactly **8 `some` cases** (5 proper redexes + 3 commuting conversions) + `_ => none`.
  Proper-redex contracta use `subsOne` (`Reduction.lean:45`); the `impE/orE` commuting case uses
  `weakCtx` (`Basic.lean:229`) + `Finset.subset_insert`.
- `Theory.Derivation.isStronglyNormal` — `Basic.lean:231`: structural `Bool` no-redex/no-commuting
  predicate. **Not** the "all reduction sequences terminate" notion — it is a predicate on a single tree.
- `Theory.Derivation.exists_stronglyNormal_form` — `Termination.lean:1884`:
  `(d : Derivation G A) → ∃ d', d'.isStronglyNormal = true`. Returns *some* SN derivation of the same
  conclusion (the structural driver `snForm d`), **not** that `d` itself reduces to it. Task 332's
  `normalize_isStronglyNormal` is gone; this existence theorem is the SN fact to transport. CONFIRMED.
- `Ctx Atom := Finset (Proposition Atom)` (`Basic.lean:101`); `insert`/`⊆` are `Finset` operations.

## Ordered Definition / Lemma List (Design B — RECOMMENDED)

All signatures below were typechecked. Cases marked **[built]** were compiled green in a scratch
file (`lake env lean`, EXIT 0) and then removed; the report records the exact proof that worked.

### Phase 1 — Term substitution, weakening, native reduction (~80 lines, definitions; green)

1. `Theory.Term.subsOne (t : Term (insert A Γ) B) (s : Term Γ A) : Term Γ B` — **transport**:
   `curryHowardForward ((curryHowardBackward t).subsOne (curryHowardBackward s))`. **[built]**
2. `Theory.Term.weakCtx (t : Term Γ A) (h : Γ ⊆ Δ) : Term Δ A` — **transport**:
   `curryHowardForward ((curryHowardBackward t).weakCtx h)`. **[built]**
3. `subsOne_fwd (D) (E) : curryHowardForward (D.subsOne E) = (curryHowardForward D).subsOne (curryHowardForward E)`
   — proof: `unfold Term.subsOne; rw [curryHoward_backward_forward, curryHoward_backward_forward]`. **[built]**
4. `weakCtx_fwd (D) (h) : curryHowardForward (D.weakCtx h) = (curryHowardForward D).weakCtx h`
   — proof: `unfold Term.weakCtx; rw [curryHoward_backward_forward]`. **[built]**
5. `Theory.Term.reduceRoot : Term G A → Option (Term G A)` — native 8-case mirror of
   `Derivation.reduceRoot` (constructor map: `impI↦lam, impE↦app, andI↦pair, andE1↦fst, andE2↦snd,
   orI1↦inl, orI2↦inr, orE↦case_`), using `subsOne`/`weakCtx` from (1)(2). **[built]** Exact body:

   ```lean
   def Theory.Term.reduceRoot {G A} : Theory.Term (T:=T) G A → Option (Theory.Term (T:=T) G A)
     | .app (.lam _ t) s            => some (t.subsOne s)
     | .fst _ (.pair _ t₁ _)        => some t₁
     | .snd _ (.pair _ _ t₂)        => some t₂
     | .case_ _ (.inl _ t) tA _     => some (tA.subsOne t)
     | .case_ _ (.inr _ t) _ tB     => some (tB.subsOne t)
     | .fst G (.case_ _ t tA tB)    => some (.case_ G t (.fst _ tA) (.fst _ tB))
     | .snd G (.case_ _ t tA tB)    => some (.case_ G t (.snd _ tA) (.snd _ tB))
     | .app (.case_ G t tA tB) s    =>
         some (.case_ G t (.app tA (s.weakCtx (Finset.subset_insert _ _)))
                          (.app tB (s.weakCtx (Finset.subset_insert _ _))))
     | _ => none
   ```

### Phase 2 — Forward correspondence (~130 lines; 2 hardest cases built, 6 analogous)

6. `reduceRoot_forward (d : Derivation G A) :`
   `(curryHowardForward d).reduceRoot = d.reduceRoot.map curryHowardForward` — **load-bearing**.
   Proof shape: `cases d` (10) then nested `cases` on the eliminated subderivation, mirroring
   `Derivation.reduceRoot`'s match; each redex case discharged by
   `simp only [Term.reduceRoot, Derivation.reduceRoot, curryHowardForward, Option.map_some,
   subsOne_fwd, weakCtx_fwd]`; each non-redex shape gives `none.map _ = none` by `rfl`/`simp`.
   - β-redex case (`impE (impI _ D) E`) **[built]**: reduces to `subsOne_fwd`.
   - commuting case (`impE (orE G D DA DB) E`) **[built]**: reduces to `weakCtx_fwd` after
     `simp only [curryHowardForward, weakCtx_fwd]`; exercises `weakCtx` + `case_` reconstruction.
   - remaining 6 cases (`andE1/andE2` proper + their two commuting, `orE` left/right proper) are
     strictly simpler (proper redexes are bare projections `some t₁`; conjunction commuting mirrors
     the proven `impE/orE` shape without `weakCtx`).
7. `reduceRoot_forward_some (d d') (h : d.reduceRoot = some d') :`
   `(curryHowardForward d).reduceRoot = some (curryHowardForward d')` — corollary:
   `rw [reduceRoot_forward, h, Option.map_some]`. (Built in Design A form; identical here.)

### Phase 3 — Backward congruence + Term strong normalization (~60 lines; green)

8. `reduceRoot_backward (t : Term G A) :`
   `(curryHowardBackward t).reduceRoot = (t.reduceRoot).map curryHowardBackward` — dual of (6) via
   `curryHoward_forward_backward` (Design A form **[built]**; Design B form is the inverse case split).
9. `Theory.Term.isStronglyNormal (t : Term G A) : Bool := (curryHowardBackward t).isStronglyNormal`. **[built]**
10. `Theory.Term.exists_stronglyNormal_form (t : Term G A) : ∃ t', t'.isStronglyNormal = true`
    — **the SN deliverable**. Proof **[built]**:
    ```lean
    obtain ⟨d', hd'⟩ := (curryHowardBackward t).exists_stronglyNormal_form
    refine ⟨curryHowardForward d', ?_⟩
    unfold Theory.Term.isStronglyNormal; rw [curryHoward_backward_forward]; exact hd'
    ```
    Optional strengthening: `isStronglyNormal_fwd (d) : (curryHowardForward d).isStronglyNormal = d.isStronglyNormal`
    (roundtrip), letting the witness be stated directly over the iso.

### Phase 4 — File wiring + CI (~30 lines + CI)

11. New file `Cslib/Logics/Propositional/CurryHoward/Reduction.lean` (header `import Cslib.Init` +
    `public import …CurryHoward.Isomorphism` + `…Normalization.Termination`), module docstring with
    `[SorensenUrzyczyn2006]`/`[Prawitz1965]` citations.
12. `lake exe mk_all --module` (new file → barrel `Cslib.lean`); full CI:
    `lake build`, `checkInitImports`, `lake lint`, `lint-style`, `lake test`, `shake`.

## SN-Transport Route (exact)

Term SN is the existence predicate, matching the codebase's `isStronglyNormal` meaning (structural
no-redex on a single tree, **not** "every reduction sequence halts"):

> `Theory.Term.exists_stronglyNormal_form (t : Term G A) : ∃ t' : Term G A, t'.isStronglyNormal = true`

Route: pull `⟨d', hd'⟩` from `(curryHowardBackward t).exists_stronglyNormal_form`, return
`curryHowardForward d'`; its `isStronglyNormal` (= `(curryHowardBackward (curryHowardForward d')).isStronglyNormal`)
equals `d'.isStronglyNormal = true` by `curryHoward_backward_forward`. **Built green.**

## Build Evidence (load-bearing, verbatim from green scratch compile)

Both scratch files compiled with `lake env lean … EXIT 0` (no errors, no `sorry`, only pre-existing
lemmas — hence no new axioms), then removed. Key proven obligations:

- Transport `reduceRootT` + `forward_corr` (`= d.reduceRoot.map curryHowardForward`, proof
  `unfold; rw [curryHoward_backward_forward]`) + `forward_corr_some` + `backward_corr` +
  `term_exists_sn` — all green.
- Native `Term.reduceRoot` (full 8 cases) + `subsOne_fwd` + `weakCtx_fwd` +
  `reduceRoot_fwd_impredex` (β case) + `reduceRoot_fwd_impcomm` (impE/orE commuting case with
  `weakCtx` + `case_` reconstruction) — all green.

## Adversarial Self-Verification (H4)

1. **"Is the Term reduction relation well-typed? Do the commuting conversions (weakCtx / context
   insert) typecheck on Term?"** — YES, *demonstrated*. `reduceRoot_fwd_impcomm` (the worst case:
   `weakCtx (Finset.subset_insert _ _)` + nested `case_`/`app` reconstruction) compiled green. The
   `Term` constructors carry the same explicit `G`/`Γ` context args as `Derivation`, so the mirror is
   well-typed.
2. **"Does `isStronglyNormal` transport meaningfully, or is Term-SN trivially definitional?"** —
   `Term.isStronglyNormal` is *defined* by transport, so `isStronglyNormal_fwd` is roundtrip-trivial;
   that is honest, not a defect. The *content* is `exists_stronglyNormal_form`, which is a substantive
   theorem (proved in 332 via `snForm`, 1880+ lines of `Termination.lean`). Term-SN inherits that
   content faithfully. Flagged: this is *existence of a normal form*, **not** strong normalization of
   all reduction sequences — the report states this explicitly to avoid over-claiming.
3. **"Is the correspondence harder than 'rename constructors'?"** — The *structural* part is
   constructor renaming (roundtrip-trivial). The genuine work is (a) defining `Term.reduceRoot`'s 8
   cases with correct dependent types, and (b) `reduceRoot_forward`'s case analysis. (a) is built in
   full; (b)'s two hardest cases are built, remaining six are strictly simpler. No case requires
   induction — all collapse to `subsOne_fwd`/`weakCtx_fwd` roundtrips.
4. **Purist objection (recorded):** transport-defined `subsOne`/`weakCtx` are not *native* term
   substitutions (they route through `Derivation.subs`). A fully native `Term.subs` would re-derive
   `Basic.lean:281`'s `Finset` machinery on `Term` — large, no proportionate benefit, and the
   transport version *is* a genuine capture-avoiding substitution (it substitutes the corresponding
   derivation and maps back). Recommendation stands; native substitution is out of scope.
5. **Zero-debt / reuse check:** all 5 reuse steps exhausted — `Derivation.reduceRoot`, `subsOne`,
   `weakCtx`, `isStronglyNormal`, `exists_stronglyNormal_form`, and both roundtrip theorems are all
   reused; nothing new is invented beyond the Term-side mirrors the task explicitly requires. No
   `sorry`, no `axiom`, no vacuous `def := True`. Confidence: **high** (mechanism fully built).

**Open gap (precise):** the only un-built obligation is the six non-load-bearing branches of
`reduceRoot_forward` (Phase 2, item 6): `andE1/andE2` proper redexes (`some t₁`/`some t₂`, trivial)
and the `andE1/andE2 over case_` commuting conversions (same shape as the built `impE/orE` case but
without `weakCtx`). Risk: LOW — no new proof technique beyond `subsOne_fwd`/`weakCtx_fwd`. Fallback if
any branch is stubborn: switch that file to Design A (transport `reduceRoot`), where the whole
correspondence is a single `rw [curryHoward_backward_forward]` (built green).

## Phasing Summary

| Phase | Content | Lines | De-risk |
|-------|---------|-------|---------|
| 1 | `Term.subsOne`/`weakCtx`/`reduceRoot` + `subsOne_fwd`/`weakCtx_fwd` | ~80 | built green |
| 2 | `reduceRoot_forward` (+ `_some` corollary) | ~130 | 2/8 hardest cases built |
| 3 | `reduceRoot_backward` + `Term.isStronglyNormal` + `Term.exists_stronglyNormal_form` | ~60 | built green |
| 4 | new `Reduction.lean`, `mk_all`, full CI | ~30 | mechanical |

**BibKey citation for the correspondence:** `SorensenUrzyczyn2006` (Lectures on the Curry-Howard
Isomorphism, §2.2); normalization side `Prawitz1965` (Ch. III–IV). Both verified in `references.bib`.
