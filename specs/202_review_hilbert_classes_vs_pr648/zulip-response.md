# Response

## Matthew

Hi Matthew, that's a great question. The core `Valuation` type needs to stay `Atom → Prop` because the canonical model construction in strong completeness uses `fun p => atom p ∈ S` where `S` is an MCS built via Lindenbaum/Zorn — that set membership is inherently `Prop`-valued with no `DecidablePred`. The same `→ Prop` convention runs through the modal, temporal, and bimodal Kripke semantics.

To get `Bool` for DPLL, I think the answer is both: add a `BoolEvaluate : (Atom → Bool) → Proposition Atom → Bool` alongside the existing `Evaluate`, with a bridge lemma `BoolEvaluate v φ = true ↔ Evaluate (fun a => v a = true) φ`. That's a small addition that gives you computable evaluation connected to the existing metatheory.

I've added both layers to [PR 648](https://github.com/leanprover/cslib/pull/648): `Semantics/Basic.lean` defines the `Prop`-valued `Evaluate` and `Tautology`, and `Semantics/Bool.lean` adds `BoolEvaluate` with the bridge lemma and a decidability instance. Happy to adjust if you'd rather structure it differently for your DPLL module, or feel free to stack a PR on it. Let me know!

## Follow Up

Regarding the smaller PR with strong soundness — PR 648 now includes the assignment semantics you'd need, so that part is covered. Strong soundness for bivalent semantics is [`prop_strong_soundness`](https://github.com/benbrastmckie/cslib/blob/main/Cslib/Logics/Propositional/Metalogic/StrongCompleteness.lean#L386), which will roll out with PR 5 in the contribution roadmap. If you need it sooner, feel free to stack a PR on top of 648 — the proof is straightforward and doesn't require the completeness machinery in that file.
