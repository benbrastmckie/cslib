# Zulip draft — modal formula base proposal to @fmontesi

**Thread**: CSLib > Modal Logic (reply to the existing #607/#662 discussion)
**Status**: DRAFT — do NOT post until (a) the standalone base patch is confirmed building green off the current #607 head, and (b) the user approves. fmontesi returns 23 July. Re-verify #607/#648/#662 states before posting (they may have moved).

---

Hi @fmontesi — one design question for whenever you're back, no rush.

I'm about to start contributing the modal **metalogic** (Hilbert calculus → soundness → completeness, building on your semantic cube). For the proof theory to stay clean, the modal `Proposition` really wants `⊥` and `→` as **primitive** constructors — the axiom schemata (`A → (B → A)`, `⊥ → A`) and the derivation-tree induction are much nicer when they're constructors rather than derived. Concretely I'd propose moving the modal type from your current `{atom, not, and, diamond}` to:

```lean
inductive Proposition (Atom) where
  | atom | bot | imp | and | or | box | diamond    -- ¬A := A → ⊥
```

i.e. `⊥`/`→`/`∧`/`∨`/`□`/`◇` primitive, `¬` the one derived connective. (This also lines the modal type up with the propositional one in #648, so the eventual `FromPropositional` embedding is constructor-to-constructor.)

**The honest tradeoff**: this is the opposite of the choice you made for the *semantics*. Making `⊥`/`→` primitive means `¬` and `∧` become **derived**, so your `not_iff_not` / `and_iff_and` go from `Iff.rfl` to one-line lemmas, and `Satisfies.dual` (`◇ ↔ ¬□¬`) becomes a small proof rather than defeq. It's a real cost on the semantic side; I think it's worth it for the metalogic, but it's genuinely your call since it's your type.

**Since it's your type, I don't want to reshape it out from under you** — but I also don't want to hand you a chore. So I've done the Lean work already: it's a small standalone patch **off your #607** (just the `Proposition` reshape in `Basic`/`Denotation`/`LogicalEquivalence`, no cube changes, builds green, zero `sorry`/new axioms). Whatever's easiest for you:
- take it into #607 as your own commit (I'll send the patch / open a PR against your branch), or
- tell me to keep it in #662, or
- suggest a different base — happy to adapt.

Related: this is the same `⊥`-primitive question that #648 raises on the **propositional** side (your `atom ⊥` under `[Bot Atom]` vs a primitive `bot`). It'd be nice to settle both together — I'd value your and @Thomas Waring's read on standardising one `⊥` design across the propositional and modal types.

Everything else can wait for the call after the 23rd. Enjoy the time off!

---

*AI disclosure (per CONTRIBUTING.md): the accompanying patch was prepared with Claude Code under my direction and verified with `lake build`/`test` + `lean-lsp`; this will be noted in the PR description.*
