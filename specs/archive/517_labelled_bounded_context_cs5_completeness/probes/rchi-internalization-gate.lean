import Cslib.Init
import Cslib.Logics.Modal.Metalogic.Constructive.Labelled.Context

/-! # Task 517 Phase 20 — PRE-GATE: does `TClosure` support the `(R_Υ)` internalization?

**VERDICT: YES.** Every claim below is sorry-free.

## What Lemma 5.3.1 actually needs (Simpson1994, p. 92, read from PDF layout)

The `clModel` discharge in Lemma 5.3.1's first paragraph rests on exactly one inference:

> "Then it cannot be the case that `Δ ⊢_{H₁} x:A` and ... and `Δ ⊢_{H_m} x:A`, because if it
> were then `Δ ⊢_H x:A` would be derivable by an application of `(R_χ)`."

For a **quantifier-free** `χ` (`ȳ` empty, so `m = 1` and the witness vector `v_{χz̄}` is empty),
p. 92's — OCR-dropped, PDF-recovered — definition

> `H_i = H ∪ {v | v ∈ v_{χz̄}} ∪ {R_{i1}[z̄/x̄][v_{χz̄}/ȳ], ..., R_{in_i}[z̄/x̄][v_{χz̄}/ȳ]}`

collapses to `H₁ = H ∪ {c}`, where `c` is the axiom's single conclusion edge. So `(R_χ)` is the
**admissible rule**

  `Δ ⊢_{H ∪ {c}} x:A`  and  `χ`'s premises hold in `H`   ⟹   `Δ ⊢_H x:A`.

## Why `TClosure` supports it

`(□E)` and `(diaI)` are, by inspection, the **only** `NIK` rules with a relational premise, and
both range over `TClosure 𝒯 G.R` rather than over `G.R` (`Deduction.lean:237-256`). `NIK` never
consults `G.X` at all. Hence derivability depends on the graph **only** through its 𝒯-closure,
and `(R_χ)` reduces to the absorption fact

  `TClosure 𝒯 G.R c` ⟹ `TClosure 𝒯 (G.addEdge c).R = TClosure 𝒯 G.R`

— adding an edge the closure already derives does not change the closure. That is `TClosure`'s
whole design intent, recorded verbatim in `GeomAxiom`'s docstring (`Deduction.lean:117-126`):
every constructor is universal Horn, which "lets `TClosure` realize `(R_χ)` for **every** `χ` in
this type by a pure relational closure".

`TS5 = {T, B, Four}` is quantifier-free throughout (post-Phase-18: `Five ∉ TS5`), so the three
instances at the bottom of this file are the complete `(R_Υ)` obligation for leg A.
-/

namespace Cslib.Logic.Modal.Labelled

universe u
variable {Atom : Type u} {𝒯 : Set GeomAxiom}

/-! ## 1. Closure absorption — the mathematical core of `(R_χ)` -/

/-- **Absorption**: if `c₁Rc₂` is already in the 𝒯-closure of `G.R`, then adding it as a literal
edge adds nothing to the closure. This is the exact content of `H₁ = H` in Simpson's maximality
step for a quantifier-free axiom. -/
theorem TClosure.absorb_addEdge {G : Graph Atom} {c₁ c₂ : Label Atom}
    (hc : TClosure 𝒯 G.R c₁ c₂) {x y : Label Atom}
    (h : TClosure 𝒯 (G.addEdge c₁ c₂).R x y) : TClosure 𝒯 G.R x y := by
  induction h with
  | base h =>
      rcases h with h | ⟨rfl, rfl⟩
      · exact .base h
      · exact hc
  | refl h x => exact .refl h x
  | symm h _ ih => exact .symm h ih
  | trans h _ _ ihxy ihyz => exact .trans h ihxy ihyz
  | eucl h _ _ ihxy ihxz => exact .eucl h ihxy ihxz

/-! ## 2. Closure-level weakening — `NIK` only sees the graph through its 𝒯-closure -/

/-- The **closure-level** graph order: `G` is below `G'` iff `G`'s 𝒯-closure is contained in
`G'`'s. Strictly weaker than `Graph.le` (which compares raw edges *and* nodes), and it is all
that `NIK` can observe. -/
def ClLe (𝒯 : Set GeomAxiom) (G G' : Graph Atom) : Prop :=
  ∀ x y, TClosure 𝒯 G.R x y → TClosure 𝒯 G'.R x y

theorem ClLe.of_le {G G' : Graph Atom} (h : G ≤ G') : ClLe 𝒯 G G' :=
  fun _ _ hxy => TClosure.mono h.2 hxy

/-- `ClLe` is a congruence for `addEdge` — needed for the `(□I)`/`(◇E)` eigenvariable cases. -/
theorem ClLe.addEdge {G G' : Graph Atom} (h : ClLe 𝒯 G G') (x y : Label Atom) :
    ClLe 𝒯 (G.addEdge x y) (G'.addEdge x y) := by
  intro a b hab
  induction hab with
  | base hb =>
      rcases hb with hb | ⟨rfl, rfl⟩
      · exact TClosure.mono (fun _ _ h' => Or.inl h') (h _ _ (.base hb))
      · exact .base (Or.inr ⟨rfl, rfl⟩)
  | refl hr z => exact .refl hr z
  | symm hs _ ih => exact .symm hs ih
  | trans ht _ _ ihxy ihyz => exact .trans ht ihxy ihyz
  | eucl he _ _ ihxy ihxz => exact .eucl he ihxy ihxz

/-- **Closure-level weakening**: `NIK` is monotone in the 𝒯-closure of the graph, not merely in
`Graph.le`. This strengthens `NIK.weaken` exactly where Lemma 5.3.1 needs it: the graph may
*shrink* as a raw edge set, provided its closure does not. -/
theorem NIK.weakenCl {G G' : Graph Atom} {Γ Δ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (h : NIK 𝒯 G Γ φ) (hG : ClLe 𝒯 G G') (hΓ : ∀ ψ ∈ Γ, ψ ∈ Δ) :
    NIK 𝒯 G' Δ φ := by
  induction h generalizing G' Δ with
  | assumption G Γ φ hmem => exact .assumption G' Δ φ (hΓ _ hmem)
  | efq G Γ x A _ ih => exact .efq G' Δ x A (ih hG hΓ)
  | andI G Γ x A B _ _ ihA ihB => exact .andI G' Δ x A B (ihA hG hΓ) (ihB hG hΓ)
  | andE1 G Γ x A B _ ih => exact .andE1 G' Δ x A B (ih hG hΓ)
  | andE2 G Γ x A B _ ih => exact .andE2 G' Δ x A B (ih hG hΓ)
  | orI1 G Γ x A B _ ih => exact .orI1 G' Δ x A B (ih hG hΓ)
  | orI2 G Γ x A B _ ih => exact .orI2 G' Δ x A B (ih hG hΓ)
  | orE G Γ x A B C _ _ _ ihor ihA ihB =>
      refine .orE G' Δ x A B C (ihor hG hΓ) (ihA hG ?_) (ihB hG ?_)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
      · intro ψ hψ
        rcases List.mem_cons.mp hψ with rfl | hψ
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impI G Γ x A B _ ih =>
      refine .impI G' Δ x A B (ih hG ?_)
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)
  | impE G Γ x A B _ _ ihimp ihA => exact .impE G' Δ x A B (ihimp hG hΓ) (ihA hG hΓ)
  | boxE G Γ x y A hR _ ih => exact .boxE G' Δ x y A (hG _ _ hR) (ih hG hΓ)
  | boxI L hL G Γ x A _ ih =>
      refine .boxI L hL G' Δ x A ?_
      intro y hy
      exact ih y hy (hG.addEdge x y) hΓ
  | diaI G Γ x y A hR _ ih => exact .diaI G' Δ x y A (hG _ _ hR) (ih hG hΓ)
  | diaE L hL G Γ x z A B _ _ ihdia ih =>
      refine .diaE L hL G' Δ x z A B (ihdia hG hΓ) ?_
      intro y hy
      refine ih y hy (hG.addEdge x y) ?_
      intro ψ hψ
      rcases List.mem_cons.mp hψ with rfl | hψ
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hΓ _ hψ)

/-! ## 3. `(R_χ)`, internalized -/

/-- **`(R_χ)` for a quantifier-free axiom, in full generality.** If the conclusion edge `c₁Rc₂`
is 𝒯-derivable from `G`'s edges, then a derivation over `G ∪ {c₁Rc₂}` can be replayed over `G`
itself. This *is* Simpson's "`Δ ⊢_H x:A` would be derivable by an application of `(R_χ)`", and
its contrapositive is the `(H₁, Δ) ∈ C` step. -/
theorem NIK.geomInternalize {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} {c₁ c₂ : Label Atom} (hc : TClosure 𝒯 G.R c₁ c₂)
    (h : NIK 𝒯 (G.addEdge c₁ c₂) Γ φ) : NIK 𝒯 G Γ φ :=
  h.weakenCl (fun _ _ hxy => TClosure.absorb_addEdge hc hxy) (fun _ hψ => hψ)

/-! ## 4. The three `TS5` instances — the complete `(R_Υ)` obligation for leg A

Post-Phase-18, `TS5 = {T, B, Four}` and `Five ∉ TS5`, so these three exhaust `𝒯`.
-/

/-- `(R_χ_T)`: reflexivity. No premises; the conclusion edge is `zRz`. -/
theorem NIK.geomInternalize_T {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (hT : GeomAxiom.T ∈ 𝒯) (z : Label Atom)
    (h : NIK 𝒯 (G.addEdge z z) Γ φ) : NIK 𝒯 G Γ φ :=
  NIK.geomInternalize (.refl hT z) h

/-- `(R_χ_B)`: symmetry. Premise `xRy` holds in `G`; the conclusion edge is `yRx`. -/
theorem NIK.geomInternalize_B {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (hB : GeomAxiom.B ∈ 𝒯) {x y : Label Atom} (hxy : G.R x y)
    (h : NIK 𝒯 (G.addEdge y x) Γ φ) : NIK 𝒯 G Γ φ :=
  NIK.geomInternalize (.symm hB (.base hxy)) h

/-- `(R_χ_4)`: transitivity. Premises `xRy`, `yRz` hold in `G`; the conclusion edge is `xRz`. -/
theorem NIK.geomInternalize_Four {G : Graph Atom} {Γ : List (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} (hF : GeomAxiom.Four ∈ 𝒯) {x y z : Label Atom} (hxy : G.R x y)
    (hyz : G.R y z) (h : NIK 𝒯 (G.addEdge x z) Γ φ) : NIK 𝒯 G Γ φ :=
  NIK.geomInternalize (.trans hF (.base hxy) (.base hyz)) h

/-! ### At the fixed target theory `𝒯 = TS5` -/

example {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    (z : Label Atom) (h : NIK TS5 (G.addEdge z z) Γ φ) : NIK TS5 G Γ φ :=
  NIK.geomInternalize_T GeomAxiom.T_mem_TS5 z h

example {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    {x y : Label Atom} (hxy : G.R x y) (h : NIK TS5 (G.addEdge y x) Γ φ) : NIK TS5 G Γ φ :=
  NIK.geomInternalize_B GeomAxiom.B_mem_TS5 hxy h

example {G : Graph Atom} {Γ : List (LabelledFormula Atom)} {φ : LabelledFormula Atom}
    {x y z : Label Atom} (hxy : G.R x y) (hyz : G.R y z) (h : NIK TS5 (G.addEdge x z) Γ φ) :
    NIK TS5 G Γ φ :=
  NIK.geomInternalize_Four GeomAxiom.Four_mem_TS5 hxy hyz h

/-! ## 5. The `Deriv`/`Context.le` chain-closure side

`Deriv 𝒯 G Γ φ` is `NIK` from *some finite sublist* of `Γ`, so `(R_χ)` lifts to `Deriv`
verbatim: the finite witness list is untouched by the graph replay.
-/

theorem Deriv.geomInternalize {G : Graph Atom} {Γ : Set (LabelledFormula Atom)}
    {φ : LabelledFormula Atom} {c₁ c₂ : Label Atom} (hc : TClosure 𝒯 G.R c₁ c₂)
    (h : Deriv 𝒯 (G.addEdge c₁ c₂) Γ φ) : Deriv 𝒯 G Γ φ := by
  obtain ⟨Γ₀, hΓ₀, hd⟩ := h
  exact ⟨Γ₀, hΓ₀, NIK.geomInternalize hc hd⟩

/-! ## 6. A SEPARATE obstruction the pre-gate uncovered: `clModel` is over-strong

`(R_Υ)` is fine (§1-§5). But `TPrime.clModel : ClassicalModel 𝒯 G.R` (`Context.lean:217`) is
**not the statement Simpson discharges**, and is not dischargeable by his argument.

Simpson p. 94, verbatim, defining the canonical model:

> `D^𝒯_(H,Δ) = the underlying set of H`,  `R^𝒯_(H,Δ)(x,y) iff xRy in H`
> "for all `(H,Δ) ∈ W^𝒯`, `(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) ⊨_CL 𝒯` **because
> `(D^𝒯_(H,Δ), R^𝒯_(H,Δ)) = H`** and `H ⊨_CL 𝒯` as `(H,Δ)` is 𝒯-prime."

So `H ⊨_CL 𝒯` is classical satisfaction **in the structure `H`**, whose domain is `H`'s
underlying set. Its quantifiers range over `H.X`. CSLib's `GeomAxiom.Holds`
(`Deduction.lean:138-143`) instead quantifies over the **whole `Label Atom` type**.

That gap is not cosmetic: Lemma 5.3.1's Zorn poset `C` fixes one coinfinite `V'` and admits only
contexts whose underlying set lies in `W(V')` (p. 92). For `z ∉ W(V')`, `H ∪ {zRz}` is **not in
`C`**, so maximality never forces `zRz ∈ H.R`. The type-wide statement asks for edges the
argument provably cannot deliver.
-/

/-- **Domain-relative classical modelhood** — Simpson's actual `H ⊨_CL χ`, with quantifiers
ranging over the graph's underlying set. -/
def GeomAxiom.HoldsOn (χ : GeomAxiom) (D : Set (Label Atom))
    (R : Label Atom → Label Atom → Prop) : Prop :=
  match χ with
  | .T => ∀ x ∈ D, R x x
  | .B => ∀ x ∈ D, ∀ y ∈ D, R x y → R y x
  | .Four => ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, R x y → R y z → R x z
  | .Five => ∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, R x y → R x z → R y z

/-- `H ⊨_CL 𝒯` in Simpson's sense: every axiom holds **on `H`'s underlying set**. -/
def ClassicalModelOn (𝒯 : Set GeomAxiom) (D : Set (Label Atom))
    (R : Label Atom → Label Atom → Prop) : Prop :=
  ∀ χ ∈ 𝒯, χ.HoldsOn D R

/-- The type-wide statement implies the domain-relative one, but **not conversely** (next). -/
theorem ClassicalModelOn.of_classicalModel {D : Set (Label Atom)}
    {R : Label Atom → Label Atom → Prop} (h : ClassicalModel 𝒯 R) : ClassicalModelOn 𝒯 D R := by
  intro χ hχ
  have := h χ hχ
  cases χ with
  | T => exact fun x _ => this x
  | B => exact fun x _ y _ hxy => this x y hxy
  | Four => exact fun x _ y _ z _ hxy hyz => this x y z hxy hyz
  | Five => exact fun x _ y _ z _ hxy hxz => this x y z hxy hxz

/-- **The counterexample.** A single-node, reflexive-at-that-node graph — a perfectly legitimate
Simpson structure with `H ⊨_CL {χ_T}` — refutes the type-wide `ClassicalModel {χ_T} H.R`.
So `TPrime.clModel` as currently typed is **strictly stronger** than Simpson's clause 0. -/
example : ∃ (G : Graph Atom),
    ClassicalModelOn {GeomAxiom.T} G.X G.R ∧ ¬ ClassicalModel {GeomAxiom.T} G.R := by
  refine ⟨{ X := {Label.var 0}, R := fun a b => a = Label.var 0 ∧ b = Label.var 0,
            nonempty := ⟨Label.var 0, rfl⟩, edge_mem := fun _ _ h => ⟨h.1, h.2⟩ }, ?_, ?_⟩
  · intro χ hχ
    rcases hχ with rfl
    intro x hx
    exact ⟨hx, hx⟩
  · intro h
    have := h GeomAxiom.T rfl (Label.var 1)
    exact absurd this.1 (by simp)

/-! ### The over-strong quantifier is not merely inelegant — it EMPTIES `TPrime TS5`

`Graph.edge_mem` (`Syntax.lean:119`) confines edges to `X`: `∀ x y, R x y → x ∈ X ∧ y ∈ X`.
Chain it with the type-wide `clModel`:

  `clModel .T` gives `∀ x, G.R x x`; `edge_mem` then gives `∀ x, x ∈ G.X`, i.e. `G.X = univ`.

But `Context.coinfinite` (`Context.lean:154`) demands a **coinfinite** `V'` with `G.X ⊆ W(V')`,
and `Label.InW V' (.var n) = n ∈ V'` (`Context.lean:119-121`). Coinfiniteness hands us an
`n ∉ V'`, and `Label.var n ∈ G.X = univ` then demands `n ∈ V'`. Contradiction.
-/

/-- **`TPrime TS5 Atom` is uninhabited.** Clause 0 (as typed), `Graph.edge_mem`, and
`Context.coinfinite` are jointly contradictory. Phase 21 cannot construct the object Lemma 5.3.1
is supposed to produce — not because the mathematics fails, but because clause 0 is transcribed
with the wrong quantifier range. **This is a statement-level defect, and it is repairable**
(swap `ClassicalModel 𝒯 G.R` for `ClassicalModelOn 𝒯 G.X G.R`); `Phase 20` does not apply the
repair, since mainline `Cslib/` is out of its territory. -/
theorem tPrime_TS5_false (P : TPrime TS5 Atom) : False := by
  obtain ⟨V', hV', hX⟩ := P.coinfinite
  obtain ⟨n, hn⟩ := hV'.nonempty
  have hrefl : P.G.R (Label.var n) (Label.var n) :=
    P.clModel GeomAxiom.T GeomAxiom.T_mem_TS5 (Label.var n)
  exact hn (hX _ (P.G.edge_mem _ _ hrefl).1)

/-- Restated as `IsEmpty`, so downstream code cannot accidentally quantify over it vacuously and
call that progress. -/
instance : IsEmpty (TPrime TS5 Atom) := ⟨tPrime_TS5_false⟩

/-- The diagnosis is precise: the emptiness is caused **solely** by `χ_T`'s quantifier range.
Under `ClassicalModelOn`, the same chain is harmless — `edge_mem` supplies exactly the `x ∈ G.X`
that the relativized clause already assumes. -/
example {G : Graph Atom} (h : ∀ x ∈ G.X, G.R x x) : ClassicalModelOn {GeomAxiom.T} G.X G.R := by
  intro χ hχ
  rcases hχ with rfl
  exact h

/-- **The repair is free at `TS5`.** `HoldsOn`/`ClassicalModelOn` cost nothing extra: `χ_B` and
`χ_4` still unfold to (domain-relative) symmetry and transitivity, exactly as
`equivalence_of_classicalModel_TS5` relies on. Phase 21 should retype clause 0 to this. -/
theorem classicalModelOn_TS5_iff {D : Set (Label Atom)} {R : Label Atom → Label Atom → Prop} :
    ClassicalModelOn TS5 D R ↔
      ((∀ x ∈ D, R x x) ∧ (∀ x ∈ D, ∀ y ∈ D, R x y → R y x) ∧
        (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, R x y → R y z → R x z)) := by
  constructor
  · intro h
    exact ⟨h GeomAxiom.T GeomAxiom.T_mem_TS5, h GeomAxiom.B GeomAxiom.B_mem_TS5,
      h GeomAxiom.Four GeomAxiom.Four_mem_TS5⟩
  · rintro ⟨hT, hB, hF⟩ χ hχ
    rcases hχ with rfl | rfl | rfl
    · exact hT
    · exact hB
    · exact hF

/-! ## 7. The tempting shortcut, and why Phase 21 must NOT take it

`ClassicalModel 𝒯 (TClosure 𝒯 R)` is **free** — three constructor applications, no maximality,
no `(R_Υ)`, no Zorn. It is recorded here precisely so that it is **not mistaken for a discharge
of `clModel`**: it proves clause 0 for the *closure* of `H`, whereas Simpson's canonical model
takes `R^𝒯_(H,Δ)(x,y) iff xRy in H` — the **raw** relation (p. 94, quoted above). Substituting
the closure would change the canonical model and put the truth lemma's `◇`-case
(which reads `G.R x y` off `TPrime.diamond`) onto a different relation than the one it is
proved about. Keep clause 0 about the raw relation; relativize its quantifiers instead.
-/

theorem classicalModel_tClosure_free (R : Label Atom → Label Atom → Prop) :
    ClassicalModel TS5 (TClosure TS5 R) := by
  intro χ hχ
  rcases hχ with rfl | rfl | rfl
  · exact fun x => .refl GeomAxiom.T_mem_TS5 x
  · exact fun _ _ hxy => .symm GeomAxiom.B_mem_TS5 hxy
  · exact fun _ _ _ hxy hyz => .trans GeomAxiom.Four_mem_TS5 hxy hyz

/-! ## 8. Scope of the blocker: Phase 21 is UNAFFECTED; Phase 23 is not

Plan v3 sequences leg A1/A2 at **`𝒯 = ∅`** first (D2, "Simpson's own order"). At `𝒯 = ∅` clause 0
is **vacuous**, so the emptiness argument of §6 cannot fire and the `(R_Υ)` obligation is empty.
The defect therefore lands on **Phase 23** (generalise to `𝒯 = TS5`), not Phase 21 — which
independently **vindicates** the plan's risk-sequencing.
-/

/-- At `𝒯 = ∅`, clause 0 is vacuously satisfiable, so §6's chain has no premise to fire on. -/
theorem classicalModel_empty (G : Graph Atom) : ClassicalModel (∅ : Set GeomAxiom) G.R := by
  intro χ hχ
  exact absurd hχ (by simp)

/-- Sharper: the emptiness is `χ_T`'s doing **alone**. `{χ_B, χ_4}` — the symmetry/transitivity
half, which is where every previous wall in this task's history stood — is vacuously satisfied by
the edgeless trivial graph, so it emphatically does *not* empty `TPrime`. -/
theorem classicalModel_B_Four_trivial :
    ClassicalModel {GeomAxiom.B, GeomAxiom.Four} (Graph.trivial Atom).R := by
  intro χ hχ
  rcases hχ with rfl | rfl
  · exact fun _ _ h => h.elim
  · exact fun _ _ _ h => h.elim

end Cslib.Logic.Modal.Labelled
