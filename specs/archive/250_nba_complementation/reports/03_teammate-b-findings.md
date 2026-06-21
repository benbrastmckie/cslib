# NBA Complementation — Teammate B Findings: Alternative Approaches

**Focus**: Indirect/compositional approaches; existing CSLib infrastructure survey

---

## Key Findings

### Finding 1: The Language-Level Complement Already Exists — But Cannot Be Directly Extracted

`Cslib.ωLanguage.IsRegular.compl` (in `Cslib/Computability/Languages/OmegaRegularLanguage.lean`)
proves that if `p` is ω-regular then `pᶜ` is ω-regular. Its proof is:

```lean
theorem IsRegular.compl {Symbol : Type} [Inhabited Symbol] {p : ωLanguage Symbol}
    (h : p.IsRegular) : (pᶜ).IsRegular := by
  obtain ⟨State, h_fin, na, rfl⟩ := h
  have : Finite (Quotient na.BuchiCongruence.eq) := buchiCongruence_fin_index
  have h_sat := buchiFamily_saturation (na := na)
  have h_cov := buchiFamily_cover (na := na)
  apply IsRegular.fin_cover_saturates_compl h_sat h_cov
  have := Language.IsRegular.congr_fin_index (c := na.BuchiCongruence)
  grind [buchiFamily, IsRegular.hmul, IsRegular.omegaPow]
```

This proof is **existential**: it establishes `∃ na', language na' = (language na)ᶜ` but does
NOT construct a specific automaton. The witness is hidden inside `IsRegular.fin_cover_saturates`
and the `grind` call. To extract the complement NBA, one would need to unfold the entire chain:

1. `IsRegular.compl` calls `fin_cover_saturates_compl`
2. Which calls `fin_cover_saturates`, which calls `IsRegular.iSup`
3. Which calls `IsRegular.inf` (intersection = complement of union of complements) and `IsRegular.hmul`
4. Each of which produces a witness NBA

The resulting NBA would be a nested sum/intersection automaton over the Büchi congruence
classes — not a clean rank-based or determinization-based automaton. Extracting it would
require making the existential proof **computationally explicit** at every step, which amounts
to rebuilding the rank-based construction from scratch anyway (since the Büchi congruence
approach IS essentially the rank-based approach at the language level).

**Verdict**: The language-level complement cannot be "pulled back" cheaply to produce a clean
complement NBA. The witness inside `IsRegular.compl` is not an explicit automaton.

---

### Finding 2: No NBA↔Language Isomorphism Exists in CSLib

There is no injective/surjective map `NBA → ωLanguage` + inverse in CSLib. The `language`
function is many-to-one (many NBAs accept the same language). The `IsRegular.iff_da_muller`
theorem — which would provide a language↔automaton round-trip via DA.Muller — is marked
`proof_wanted` and not yet proved:

```lean
/-- McNaughton's Theorem. -/
proof_wanted IsRegular.iff_da_muller {p : ωLanguage Symbol} :
    p.IsRegular ↔
    ∃ (State : Type) (_ : Finite State) (da : DA.Muller State Symbol), language da = p
```

McNaughton's theorem (= Safra determinization) is exactly what task 241 aims to prove.
Without it, there is no way to go from language-level complement back to a specific automaton.

**Verdict**: The language↔automaton round-trip route is blocked pending task 241.

---

### Finding 3: The Determinization-Based Route (via Piterman/Safra) Is Blocked by Task 241

The determinization route (determinize NBA → complement deterministic automaton → convert back)
requires:

1. A proof of `IsRegular.iff_da_muller` (McNaughton's theorem, task 241)
2. A DA.Muller complement construction (flipping the acceptance family: `F ↦ 2^Q \ F`)
3. Converting DA.Muller back to NBA

Step 2 would be trivial once determinization exists. Step 3 is provided by `IsRegular.of_da_buchi`
(for DA.Buchi) and the equivalence of Büchi/Muller/Rabin nondeterministic automata (referenced
in Thomas 1997, Proposition 5.3). However, none of these pieces currently exist in CSLib for
the omega-word case. The Piterman 2007 paper is a Safra variant that produces a **deterministic
parity automaton** from an NBA — then complement is a parity flip. This is cleaner theoretically
but equally blocked.

**Evidence from Piterman 2007**: The paper (p. 1-2) notes: "Büchi showed that the class of
languages recognized by nondeterministic Büchi automata is closed under complement without
determinization. Sistla, Vardi, and Wolper suggested a singly exponential complementation
construction, however with a quadratic exponent. This was followed by a complementation
construction by Klarlund and a very elegant complementation via alternating automata by
Kupferman and Vardi."

Piterman explicitly treats determinization and complementation as separate routes, and notes
that "complementation constructions that are much simpler than determinization" exist.

**Verdict**: Determinization-based route requires task 241 (McNaughton/Piterman); blocked as
a prerequisite dependency.

---

### Finding 4: No Intersection + Determinization Shortcut Exists

The idea "complement via intersection + determinization" would need: for each regex U·V^ω
in the Büchi congruence decomposition, compute their complements and intersect. But:

- CSLib has `NA.Buchi` intersection via `BuchiInter.lean` (the "history bit" product construction)
- But computing the complement of each U·V^ω piece still requires complementing an NBA
  (circular dependency), OR using the DFA complement for the finite parts and then some
  omega-closure complement argument

There is no shortcut here. The Büchi congruence approach used in `IsRegular.compl` IS the
closure-under-complement proof — it just does not yield a concrete automaton.

**Verdict**: No compositional shortcut via existing CSLib intersection infrastructure.

---

### Finding 5: CSLib Has No Existing Formalization of NBA Complement — in Any Form

Exhaustive search via `lean_local_search` confirms:
- No `Buchi.complement` declaration
- No `NBA.compl` or similar
- No `DA.Muller.complement` (no DA.Muller complement construction either)
- Only `ωLanguage.IsRegular.compl` (purely existential, no automaton extracted)
- Only `Cslib.Language.IsRegular.compl` (for finite-word DFA, in RegularLanguage.lean —
  this IS constructive via `DFA.instCompl`, but for finite words only)

For **finite words**, Mathlib has a concrete `DFA.instCompl` instance that flips the accept set.
No analogous construction exists in CSLib for omega-words.

---

### Finding 6: Thomas 1997 Confirms Two Independent Routes — Neither Has a Hidden Shortcut

Thomas 1997 (Section 5.1–5.2) confirms the two independent approaches to complementation:

1. **Büchi's original approach** (congruence-based): "uses a representation of Büchi recognizable
   sets in the form ∪ᵢ Uᵢ·Vᵢ^ω, where Uᵢ, Vᵢ are classes of a sufficiently fine congruence
   over A of finite index, and applies a combinatorial argument (e.g., a form of Ramsey's
   Theorem) to guarantee that the complement has again such a representation."

2. **Determinization route**: "proceed to deterministic automata... deterministic Muller automata
   are equivalent in expressive power to (nondeterministic) Büchi automata. The complementation
   result follows, because the class of ω-languages recognized by deterministic Muller automata
   is clearly closed under complement. (In an automaton with state set Q and system F of final
   state sets, proceed to 2^Q \ F.)"

Thomas notes (p. 30): "This approach does not work when the Büchi acceptance condition is
employed. (For example, a deterministic Büchi automaton recognizes the set of ω-words over
{a,b} with infinitely many occurrences of a, but no deterministic Büchi automaton recognizes
the complement of this set.)"

This confirms the fundamental difficulty: NBA complementation cannot be done by simply flipping
the acceptance set, and no elementary trick avoids either the rank-based construction or
full determinization.

---

### Finding 7: No Lean 4 or Coq Formalization of Büchi Complement Found

A search via `lean_leansearch` for "complement nondeterministic Büchi automaton rank-based
construction Lean" returns only DFA/finite-word results. No existing Lean 4 formalization of
NBA complement was found. Mathlib's `Computability.DFA` has `DFA.instCompl` but nothing for
NBA or ω-word automata.

Isabelle/HOL has a Büchi complement formalization (in the Verified Model Checker project), but
this is not available in Lean 4.

---

## Recommended Approach

### Primary Recommendation: Direct Rank-Based Construction (Kupferman-Vardi)

The rank-based approach (Teammate A's focus) is the **only viable standalone approach** given
CSLib's current state. It does not require task 241 (determinization), it has the cleanest
self-contained correctness proof, and it is the approach the literature recommends for first
formalizations.

There is **no compositional shortcut** available that would let us avoid a direct construction.
Specifically:

- The language-level complement (`IsRegular.compl`) cannot be extracted into an automaton
  without rebuilding the construction
- The determinization route is blocked pending task 241
- No NBA↔language isomorphism exists in CSLib

### Secondary Recommendation: Add a `complement_language_eq` Corollary

Once the rank-based complement automaton `na.complement` is defined (State type: subset-rank
pairs, see Teammate A's work), the most valuable secondary contribution is a theorem:

```lean
theorem Buchi.complement_language_eq (na : Buchi State Symbol) :
    language na.complement = (language na)ᶜ
```

This would make the existing `IsRegular.compl` derivable as a corollary:

```lean
-- Could replace the current existential proof:
theorem IsRegular.compl' (h : p.IsRegular) : (pᶜ).IsRegular := by
  obtain ⟨State, h_fin, na, rfl⟩ := h
  exact ⟨_, inferInstance, na.complement, na.complement_language_eq⟩
```

This strengthens `IsRegular.compl` from purely existential to computationally explicit.

### Determinization Route as Future Work (Post Task 241)

After task 241 (McNaughton), a modular complement would be:

```lean
theorem IsRegular.compl_via_det (h : p.IsRegular) : (pᶜ).IsRegular := by
  -- determinize, flip Muller acceptance family, convert back to NBA
```

This should be noted in the task 250 implementation plan as a future roadmap item, not a
dependency.

---

## Evidence Summary

| Claim | Evidence |
|-------|---------|
| Language-level complement exists but is non-constructive | `OmegaRegularLanguage.lean:249-259` |
| `IsRegular.iff_da_muller` is `proof_wanted` | `OmegaRegularLanguage.lean:261-264` |
| No `Buchi.complement` in CSLib | `lean_local_search "Buchi.complement"` → empty |
| `BuchiInter.lean` provides intersection but not complement | `NA/BuchiInter.lean:100-136` |
| No NBA↔language round-trip exists | `IsRegular.iff_da_muller` proof_wanted |
| Thomas 1997 confirms no elementary trick | `Thomas_1997_Languages_Automata_Logic.md:1330-1343` |
| Piterman 2007 confirms complementation simpler than determinization | `Piterman_2007.md:88-94` |
| Finite-word analogue (DFA) has concrete `instCompl` | Mathlib `DFA.instCompl` |

---

## Confidence Level

**High confidence** that:
1. The rank-based approach (Teammate A) is the only viable standalone path
2. There is no hidden compositional shortcut through existing CSLib infrastructure
3. The determinization route is cleanly blocked by task 241 status

**Medium confidence** that:
4. The `complement_language_eq` corollary approach (replacing existential `IsRegular.compl`)
   is achievable once Teammate A's construction is complete

**Low concern** that:
5. Alternative formalizations (slice-based, Kähler-Wilke) offer any advantage for CSLib;
   they are less well-documented and offer no infrastructure reuse benefit

---

## CSLib Infrastructure Reuse Summary

The following existing pieces CAN be reused in the rank-based implementation:

| Existing Component | Location | Role in Complement |
|-------------------|----------|--------------------|
| `NA.Buchi` structure | `NA/Basic.lean` | Input automaton type |
| `NA.iProd` | `NA/Prod.lean` | Could help for state product if needed |
| `Set.Saturates` + `saturates_compl` | `Foundations/Data/Set/Saturation.lean` | Used by `IsRegular.compl` |
| `buchiFamily_saturation` | `Languages/Congruences/BuchiCongruence.lean` | Already proves complement closure |
| `BuchiInter` (intersection) | `NA/BuchiInter.lean` | Not needed directly for rank-based |
| `NA.Buchi.reindex` | `NA/BuchiEquiv.lean` | State equivalence; universe polymorphism |

The rank-based construction needs primarily a new file `NA/BuchiCompl.lean` with a new
`State` type (subset of states × rank function) and new transition/acceptance definitions.
The `IS Regular.compl` theorem then gets a stronger constructive proof as a bonus.
