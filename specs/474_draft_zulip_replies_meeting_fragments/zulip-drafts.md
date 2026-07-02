> DRAFT — review and personalize before posting.
>
> Note: the CSLib Zulip has an AI-content policy (Chris Henson previously flagged an
> AI-drafted message as disallowed). Rewrite both of these in your own voice before
> posting — they are deliberately plain and first-person so they read as yours, not
> as generated text.
>
> Reminder (not for posting): you still owe Doty the `CPL⟨→,⊤⟩` conservativity proof.
> That's being handled separately as task 473.

---

## Draft A — reply to Fabrizio Montesi in the "Modal Logic" topic

Thanks Fabrizio, and sorry for the volume — that's on me. Happy to slow down and take the points one at a time, and to keep the PRs small going forward.

Yes, I'd be glad to join a CSLib meeting once you're back from the 23rd. Just point me at a time that works.

Quick map of where things stand so the stack makes sense:

- #648 is the propositional base: five primitives with a primitive `⊥` and efq. That design was already agreed with Thomas Waring in the Propositional Logic thread.
- #662 is the modal refactor, stacked on #648.
- For your #607, I'd rather help land it than duplicate it. Once we agree on the impl/imp naming and on the `⊥` question in `Defs.lean`, I'll rebase #648/#662 onto it in one pass.

We can walk through all of that in the meeting if that's easier than doing it in comments.

---

## Draft B — open the fragment-design discussion (raised by Matthew Doty in the Propositional Logic thread)

In the Propositional Logic thread Matthew Doty raised the fragment-design question, and #648 deliberately deferred it. I'd like to open it up before anyone builds it, since the choice affects a lot downstream.

The question: how do we represent sub-signature fragments, e.g.

    IPL⟨→,⊤⟩  ⊂  IPL⟨∧,→,⊤⟩  ⊂  ...

The main options I see are:

1. Typeclasses that gate which connectives are available.
2. Separate inductive types per fragment.
3. A single axiom-parameterized theory where the fragment is a parameter.

The hard part isn't the syntax — it's how derivations transfer between fragments (a proof in a smaller fragment should carry over to a larger one, and we want conservativity in the other direction). I've already formalized the conservativity chain, so we have something concrete to test any design against.

Before I start building, I'd like input on which of the three directions people prefer, especially from anyone who's hit this in other developments.

Question: should this be its own Zulip topic, or a GitHub issue? It's design-discussion-heavy, so I lean toward a new topic, but I'm fine opening an issue if we'd rather track it there.
