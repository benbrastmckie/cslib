> DRAFT — review and personalize before posting.
>
> Note: the CSLib Zulip has an AI-content policy (Chris Henson flagged a message as
> possibly LLM-written on 2026-06-22 and cited the policy). Rewrite both of these in your
> own voice before posting — they are deliberately plain and first-person so they read as
> yours, not as generated text.
>
> Reminder (not for posting) — UPDATED after fact-check: the `CPL⟨→,⊤⟩` conservativity
> you promised Doty on 2026-06-26 ("Definitely worth proving. I'll attend to that
> shortly.") is NO LONGER outstanding. It exists sorry-free on your local main:
> `cpl_conservative_over_imp` in
> `Cslib/Logics/Propositional/Metalogic/ClassicalImpCompleteness.lean` (Tarski–Bernays
> axioms via Kalmár-style completeness), plus the converse subsumption direction
> `derivablePropOfDerivableClassicalImp` and the combined biconditional. What remains is
> upstreaming it (and syncing task 473, which state.json still shows as [not_started]).
> You could mention to Doty that it's done when relevant. Note Doty also questioned using
> algebraic semantics vs. plain truth assignments for this fragment — the local proof
> goes through Kalmár/truth-table-style completeness, which answers that concern.

---

## Draft A — reply to Fabrizio Montesi in the "Modal Logic" topic

Thanks Fabrizio, and sorry for the volume — that's on me. Happy to slow down and take the points one at a time, and to keep the PRs small going forward.

Yes, I'd be glad to join a CSLib meeting once you're back from 23 July. Just point me at a time that works.

Quick map of where things stand so the stack makes sense:

- #648 is the propositional base: five primitives with a primitive `⊥` and efq as a rule, so IPL is the base logic. That follows the compromise Thomas Waring proposed in the Propositional Logic thread, which I've implemented there.
- #662 is the modal refactor, stacked on #648.
- For your #607, I'd rather help land it than duplicate it. Once we agree on the impl/imp naming and on the `⊥` question in `Defs.lean`, I'll rebase #648/#662 onto it in one pass.

We can walk through all of that in the meeting if that's easier than doing it in comments.

---

## Draft B — open the fragment-design discussion (per Matthew Doty's suggestion in the Propositional Logic thread)

Matthew suggested in the Propositional Logic thread that fragments deserve their own thread (and possibly an issue once a design is nailed down), so here it is. #648 deliberately deferred fragment design, and I'd like to open it up before anyone builds it, since the choice affects a lot downstream.

The question: how do we represent sub-signature fragments, e.g.

    IPL⟨→,⊤⟩  ⊂  IPL⟨∧,→,⊤⟩  ⊂  IPL⟨∧,→,⊥,⊤⟩  ⊂  IPL

The main options I see are:

1. Typeclasses that gate which connectives are available. Matthew has said he leans this way, with the caveats that it could get ad hoc, may not play well with automation, and makes conservativity of extensions harder to prove.
2. Separate inductive types per fragment.
3. A single axiom-parameterized theory where the fragment is a parameter.

The hard part isn't the syntax — it's how derivations transfer between fragments. Thomas made the point that manipulations on derivations should carry over to larger fragments by construction, from the way a fragment is specified, rather than being reproved for each. And we want conservativity in the other direction. I've already formalized the conservativity chain above, with algebraic semantics for each step (Hilbert algebras → Brouwerian semilattices → pointed Brouwerian → Heyting), so we have something concrete to test any design against.

Before I start building, I'd like input on which of the three directions people prefer, especially from anyone who's hit this in other developments. If we converge on a design here, I'll open a GitHub issue to track it, as Matthew suggested.
