# Zulip: Modal Logic

Channel: [#CSLib > Modal Logic](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Modal.20Logic)

---

**Fabrizio Montesi** (2026-05-26):
We've had a sprint at FORM on formalising modal logic and the complete modal cube, now reviewable in [cslib#528](https://github.com/leanprover/cslib/pull/528). :) Joint work with Marianna Girlando.

---

**Chris Henson** (2026-05-26):
Linking for later discoverability: [#Is there code for X? > Euclidean relation](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/Euclidean.20relation/with/591815570)

---

**Kyle Miller** (2026-05-26):
I happen to have a Lean formalization of the completeness and consistency of S5 modal logic, from following the thesis "Formalization of modal logic S5 in the Coq proof assistant" by Lubor Budaj (https://fse.studenttheses.ub.rug.nl/28482/1/BSc_Thesis_final.pdf) as an exercise, which I'm happy to get working on CSLib once this PR is merged.

---

**Fabrizio Montesi** (2026-05-26):
> Kyle Miller said:
> I happen to have a Lean formalization of the completeness and consistency of S5 modal logic...

That'd be nice! What do the main theorems look like?

---

**Kyle Miller** (2026-05-26):
@Fabrizio Montesi I didn't use any notations to make it read nicer, but completeness is

```lean
theorem completeness (G : Set Form) (f : Form)
    (hinter : ∀ (m : Model) (w : m),
      (∀ g ∈ G, m.interpret g w) → m.interpret f w) :
    ax_s5 G f
```

`m.interpret g w` is `m, w ⊨ g`, and `ax_s5 G f` is `G ⊢ f` according to S5's axioms. It uses the approach of creating the canonical model consisting of worlds of maximal consistent sets of propositions. Part of the argument uses an `Encodable` instance (generated using a Mathlib deriving handler I've already contributed) to be able to construct maximal consistent sets by enumerating propositions.

I used a `Consistency` predicate, but unfolding the definitions, consistency is `¬ (∅ ⊢ False)`:

```lean
theorem consistency : ¬ ax_s5 ∅ .ff
```

That's a consequence of soundness:

```lean
theorem soundness (G : Set Form)
    {m : Model} (w : m) (valid : ∀ g ∈ G, m.interpret g w)
    {f : Form} (hf : ax_s5 G f) :
    m.interpret f w
```

---

**Fabrizio Montesi** (2026-05-26):
Is ax_s5 a proof system then (inference rules)? Marianna Girlando and I were gonna look at it, but we haven't started yet; if you already have something to start from, all the better.

---

**Kyle Miller** (2026-05-26):
Oh yeah, it's a system of inference rules, as an inductively-defined proposition.

Here's a Gist with the complete file: https://gist.github.com/kmill/f4649908a8eb1b8e6f5cf6a2d1dee553

---

**Fabrizio Montesi** (2026-05-27):
@Chris Henson @Kyle Miller @Thomas Waring [cslib#528](https://github.com/leanprover/cslib/pull/528) should be ok now.

A couple of things are worth discussing even after the PR though, namely notation -- see [#CSLib > Notation for logical connectives](https://leanprover.zulipchat.com/#narrow/channel/513188-CSLib/topic/Notation.20for.20logical.20connectives/with/591870818) -- and which connectives should be 'primitive' in the inductive -- which I still don't understand since in general keeping the base inductive small is convenient and we have characterisation theorems for the encoded connectives, but I'm certainly curious to know more.

---

**Fabrizio Montesi** (2026-05-27):
> Kyle Miller said:
> Here's a Gist with the complete file...

Thanks. I get it now, it's the Hilbert-style axiomatisation (we should categorise it as such because we'll probably want sequent calculi as well, there are many, and they're pretty useful for algorithmic reasons as well as far as I recall).
To encode `false`, can we use the same trick @Thomas Waring used for propositional logic (`[Bot Atom]`) + the hypothesis that it never holds for any world? Many papers about modal logic use only the operators in [cslib#528](https://github.com/leanprover/cslib/pull/528) (modulo the decision or having box or diamond as primitive).

---

**Thomas Waring** (2026-05-27):
> Kyle Miller said:
> It uses the approach of creating the canonical model consisting of worlds of maximal consistent sets of propositions. Part of the argument uses an `Encodable` instance...

this is very nice! possibly interesting to you: i derived [completeness for Kripke models of intuitionistic logic](https://github.com/thomaskwaring/cslib_SKI/blob/kripke/Cslib/Logics/Propositional/Semantics/Kripke.lean#L204) from the completeness of its (Heyting-) algebraic semantics (which is relatively straightforward). there the Kripke model you construct has worlds prime filters in the Heyting algebra, and the "maximal consistent set" construction is effectively pushed into an application of [docs#DistribLattice.prime_ideal_of_disjoint_filter_ideal](https://leanprover-community.github.io/mathlib4_docs/find/?pattern=DistribLattice.prime_ideal_of_disjoint_filter_ideal#doc) (actually an easy generalisation of its dual, which i will upstream to mathlib once [#34855](https://github.com/leanprover-community/mathlib4/pull/34855) goes through)

---

**Fabrizio Montesi** (2026-05-28):
Anything else I should change in [cslib#528](https://github.com/leanprover/cslib/pull/528)? The only remaining point seems to be whether I should replace `≤` with `⊆` for ordering logics, which I'm not totally sure about (I wanted to keep hidden that a logic is a set until I have a reason not to) but I'd be fine with either.

---

**Fabrizio Montesi** (2026-05-28):
Regarding the axiomatised systems: it looks like a good use case for the approach I followed in CLL and MLL? That is, define a mega-inductive with all the axioms in the Modal Cube and instantiate `InferenceSystem` for each fragment, so that we can write `S5⇓φ`, `K⇓φ`, etc.

If we then prove soundness and completeness for these systems, we should be able to leverage the ordering results already in `Modal/Cube` to prove things like `K⇓φ → S5⇓φ` nearly for free.

---

**Thomas Waring** (2026-05-28):
imo if you want to hide that logic is a set it should not literally be a set, ie at least some `abbrev Logic := Set (Proposition Atom)`, but it's probably not a huge deal either way. the only other thing i wanted to request was more informative names for `or_char` and relatives — even `Satisfies.or_iff` would work :-)

---

**Thomas Waring** (2026-05-28):
are you intending to define a Hilbert-style derivation system? my impulse would be to do it more in the style of my natural deduction `Theory` — as there's one inductive which is parametric in a collection of axioms, with two rules (appeal to axiom, modus ponens) — but you're right that the fragment approach would also be very neat!

---

**Fabrizio Montesi** (2026-05-28):
> Thomas Waring said:
> are you intending to define a Hilbert-style derivation system?...

Not me, I was talking about @Kyle Miller's.

---

**Fabrizio Montesi** (2026-05-28):
> Thomas Waring said:
> imo if you want to hide that logic is a set...

Ah, I see, I can do that, one sec.

---

**Thomas Waring** (2026-05-28):
> Fabrizio Montesi said:
> Not me, I was talking about Kyle Miller's.

right, yes, i was just querying what sort of inference system you are looking to define, but i can also wait & see :))

---

**Fabrizio Montesi** (2026-05-28):
> Thomas Waring said:
> right, yes, i was just querying what sort of inference system you are looking to define...

We're not sure yet, we're playing with the idea that our next immediate step might be to implement a decision procedure for one of these logics and prove it correct. But that decision procedure might rely on a sequent calculus-like system. We still gotta meet & discuss this part. :)

---

**Thomas Waring** (2026-05-28):
okay cool, i look forward to seeing what you come up with

---

**Fabrizio Montesi** (2026-05-28):
By the way, we're looking for cool examples of what we could do.

> Fabrizio Montesi said:
> Ah, I see, I can do that, one sec.

Done, @Thomas Waring.

---

**Fabrizio Montesi** (2026-05-29):
New PR: in [cslib#535](https://github.com/leanprover/cslib/pull/535), I add logical equivalence for modal logic.

I've prioritised this because the class of models being considered reminds me a lot of the `Theory` in @Thomas Waring's formalisation of propositional logic, so a pattern might be emerging.

---

**Thomas Waring** (2026-05-29):
I see your point, that's reassuring :-) you seem to have done the same thing as me, and define a tagged notation for your notion of equivalence — does that mean we should update or deprecate the notation defined in `LogicalEquivalence.lean`?

---

**Fabrizio Montesi** (2026-05-30):
Well, we could update LogicalEquivalence with an extra parameter, or probably even store the assumptions about the models or theory under consideration in the notion of judgemental context. I'll play a bit more with this to understand which one works more naturally. (The second might not pan out at all; but if it does, it might give us a pretty modular approach.)

---

**Fabrizio Montesi** (2026-05-30):
at the very least we could do the parametrised approach, just like I generalised `InferenceSystem`.

---

**Thomas Waring** (2026-05-30):
the latter seems reasonable — i don't think there's any major problem with the type class itself, my comment was more about the notation, which seems not to capture all the relevant information (as evidenced by the fact we both used specific notations instead)

---

**Fabrizio Montesi** (2026-05-31):
Almost there.

In the meantime, anything else I should do to [cslib#528](https://github.com/leanprover/cslib/pull/528)?

---

**Thomas Waring** (2026-05-31):
other than deciding whether we want to hide that `logic blah` is a set, lgtm :))

---

**Fabrizio Montesi** (2026-06-01):
right, let's keep it simple for now, I'm using union and set inclusion now.

---

**Thomas Waring** (2026-06-01):
great — last quibble would be in that case maybe rename `k_leq_d` to `k_subset_d` etc, otherwise good to go

---

**Fabrizio Montesi** (2026-06-01):
ofc. done!

---

**Fabrizio Montesi** (2026-06-01):
(For a future PR:) I wonder if I should bundle the type `World` in a `Model`.
I currently define the class of 'all models on type World',

```lean
abbrev Model.Class.All World Atom := (Set.univ (α := Model World Atom))
```

which I'm not sure is correct. The class of all models should probably be the set of all models of *any* World type, right? I guess this could be recovered by doing the infinite union of these though? Is Set.iUnion what I should be looking at? But this doesn't work, and looking at it carefully I think it shouldn't because the type of the resulting set is unclear:

```lean
abbrev Model.Class.All Atom :=
  Set.iUnion (fun (World : Type*) => (Set.univ (α := Model World Atom)))
```

---

**Malvin Gattinger** (2026-06-02):
I'm very happy to see modal logic landing in CSlib and the definitions look usable to me! (I had a short chat with Marianna this afternoon, hene I took a look again now.)

One thing that confuses me is the name of `HasInferenceSystem`, because so far there are just semantics, not a proof system yet, right? So is the idea of `HasInferenceSystem` more like "this is some notion of how some judgement can be true / hold"?
And then a soundness or completeness statement later will be something that relates two instances of `InferenceSystem S α` and `InferenceSystem S' α`? :thinking:

Maybe a related small thing would be that then the docstring of `Judgement.mk` (which is the one that shows up when I hover over e.g. `Modal[m,w ⊨ φ₁ → φ₂]` could be more informative if it mentions that it is specific for modal logic / this particular semantics.

Lastly, I have a very non-important suggestion for the Modal Logic PR: use `\Diamond` instead of `\diamond` so that (in my view) box and diamond look better together, and then both vs code commands start with an upper case letter:

```lean
-- □ -- \Box
-- ◇ -- \Diamond
-- ◫ -- \box
-- ⋄ -- \diamond
```

---

**Malvin Gattinger** (2026-06-02):
And for talking about "all models using the same `Atom`" my naive guess would be this?

```lean
abbrev Model.Class.All_for Atom := Σ World : Type, (Set.univ (α := Model World Atom))
```

---

**Fabrizio Montesi** (2026-06-03):
> Malvin Gattinger said:
> One thing that confuses me is the name of `HasInferenceSystem`...

Yes, inference system is intended as a general 'way of proving that something holds', essentially. So it can be used for, say, both semantic statements and conclusions in a concrete proof system (sequent calculus, etc.).
Soundness and completeness would look like you say, though the `α` would also probably be different in the case of an axiomatisation (there you just have the proposition). But generally yes, that's the idea.

---

**Fabrizio Montesi** (2026-06-03):
Re the docstring: what would you propose?
Re the diamond: oh, I overlooked the existence of \Diamond. I'll switch to that in my next PR about this. (Edit: I'm doing it on the original PR, I got a couple of comments in there anyway.)

---

**Malvin Gattinger** (2026-06-03):
Maybe this?

```lean
structure Judgement World Atom where
  /-- Judgement `m,w ⊨ φ` says that in model `m` the world `w` satisfies the proposition `φ`. -/
  mk ::
[...]
```

Also, I first wanted to write "formula" instead of "proposition", making me realize that I find `Proposition` a strange name for the type that represents the syntax only. (But that is a matter of conventions and what books one has read I guess.)

---

**Fabrizio Montesi** (2026-06-03):
Yeah, we inherited that from some linear logic texts and then just consistent application -- across the logic and inference system literature, you'll find both.
I don't have a strong opinion (yet?), just erring on the side of consistency for now.
If we wanna elicit that a term doesn't necessarily have an interpretation, formula might be more appropriate/familiar. I haven't encountered that yet really though, but it might be because so far we've mostly formalised 'syntaxes with an intent', as in modal logic.

---

**Malvin Gattinger** (2026-06-04):
Right, I also would say keeping the terminology consistent across different logics is more important than following the conventions in (each of the different parrs of) the literature.
My own use of the words would be that any set of worlds is a proposition, and some propositions can be expressed with *formulas*. But I think you already use "Denotation" for that concept which at least for those sets of worlds that are the meaning/denotation of a formula seems clear and less ambiguous to me than "Proposition".

Another aspect might be whether it is good or bad that "Proposition" is close to the `Prop` in Lean. Phrased differently, is a Lean `Prop` a formula? Or would formulas be `Expr`?

---

**Ching-Tsun Chou** (2026-06-04):
Came across this talk on YouTube:
https://www.youtube.com/live/oiOdnGB8HMs
Perhaps it is relevant.

---

**SnO2WMaN** (2026-06-09):
Hello, I'm author of modal logic side of [FFL](https://github.com/FormalizedFormalLogic/Foundation). I didn't realize there's some progress on cslib, it's excited modal cube formalized in this!
I have some mention about this project.

1. What is current goal of this project? Our main passionate in FFL is about provability logic, I formalized GL completeness and some extra results. but we want to cover whole area of modal logic. I saw this formalization refer to Blackburn et al, so might be model/frame theoric results?
2. Currently I'm working redesigning modal logic. Dealing Kripke semantics in type theory / lean is a bit conplex about universe problem. My new designing Kripke semantics idea, is in https://github.com/SnO2WMaN/SeqPL (sequent calculus for GL).

I'm happy someone else me is working formalizing modal logic, hope for sharing idea and working with!

---

**Malvin Gattinger** (2026-06-09):
About GL, let me also mention this project by @Madeleine Gignoux https://mgignoux.github.io/lean4-gl-coalgebras/docs/GL.html - the master thesis about this was recently defended and will be available in a few weeks.

---

**SnO2WMaN** (2026-06-09):
Wow I missed this project, it sounds great :mechanical_arm:

---

**Fabrizio Montesi** (2026-06-10):
> Malvin Gattinger said:
> Another aspect might be whether it is good or bad that "Proposition" is close to the `Prop` in Lean...

If we get into the details, I guess a well-typed Lean term of type Prop is a proposition.

---

**Fabrizio Montesi** (2026-06-10):
> SnO2WMaN said:
> Hello, I'm author of modal logic side of FFL...

FFL looks really nice!

1. The broad goal for the logic part of CSLib is to have all relevant logics for CS research and software development, including semantics, proof theories (like sequent calculi), and key algorithms. Hopefully CSLib can become a place to discuss reusable abstractions that we can share.
2. What is the problem you've encountered? Everything has gone pretty smoothly during our development, but I might be missing something?...

I'd be very interested in having joint discussions on how to manage the zoo of logics and their extensions. It's a recurring problem. You can see my latest attempt at formalising a 'fragment' of a proof system in https://github.com/leanprover/cslib/blob/main/Cslib/Logics/LinearLogic/CLL/MLL.lean .

---

**Thomas Waring** (2026-06-10):
i would guess the universe issues come up once you go to first-order, no?

---

**Fabrizio Montesi** (2026-06-10):
> Thomas Waring said:
> i would guess the universe issues come up once you go to first-order, no?

Maybe? What's the key difference wrt, say, lambda calculus? Models?

---

**Chris Henson** (2026-06-10):
Just to be clear, there are also painful universe things with lambda calculi too if you try to do things like categorical semantics where you have a mismatch in universes.

---

**Thomas Waring** (2026-06-10):
right, my sense that was to define first-order Kripke models you have to associate to each world a type, so something is likely to get dependent & therefore sticky — that hasn't come up so far bc everything is propositional

---

**Alexandre Rademaker** (2026-06-11):
Hi @Benjamin Brast-McKie, maybe you can comment here about your work and suggestions in [cslib#633](https://github.com/leanprover/cslib/pull/633)?

---

**Benjamin Brast-McKie** (2026-06-11):
Yes, happy to share! I've been implementing Hilbert proof systems for the standard modal logics, establishing soundness and completeness. I've been working backwards from the Bimodal/ logic I developed which combines tense and modal operators and establishes soundness and completeness over the task semantics which models non-deterministic dynamical systems. I've still got a lot of clean up to do, and just starting to roll out PRs, but you can find what I have so far for the modal logic here: https://github.com/benbrastmckie/cslib/tree/main/Cslib/Logics/Modal

---

**Ching-Tsun Chou** (2026-06-11):
There are already quite a few PRs and existing code related to logics, including modal logics. What do you plan to do to coordinate with all that?

---

**Benjamin Brast-McKie** (2026-06-11):
Hi @fmontesi,

I submitted [PR #648](https://github.com/leanprover/cslib/pull/648), which refactors `Propositional/Defs.lean` to a five-primitive signature `{atom, bot, imp, and, or}` with connective typeclasses (`HasBot`, `HasImp`, `HasAnd`, `HasOr`) in a single [`Foundations/Logic/Connectives.lean`](https://github.com/benbrastmckie/cslib/blob/feat/propositional-v2/Cslib/Foundations/Logic/Connectives.lean). The propositional base supports minimal, intuitionistic, and classical logic where negation is derived as `φ → ⊥`.

I'm planning a follow-up for `Modal/Basic.lean` using `{atom, bot, imp, box}` with `HasBox`/`ModalConnectives`. Diamond would be derived as `¬□¬φ`, restricting this type to classical modal logic — the same restriction as the current upstream type (just dual: upstream derives box via `¬◇¬φ`). A separate `HasDia` primitive could be added later for intuitionistic modal logics (IK, CK). Box is chosen as the initial primitive because necessitation becomes a pure rule — `⊢ φ → ⊢ □φ` — mentioning only `box`. With diamond primitive, necessitation would be an interaction law: `⊢ φ → ⊢ ¬◇¬φ` (requiring `neg`), or `⊢ φ → ⊢ (◇(φ → ⊥)) → ⊥` (requiring `dia`, `imp`, and `bot`). The K axiom is similar: `□(φ → ψ) → □φ → □ψ` uses only `box` and `imp`, while its diamond dual mixes more connectives. This also aligns with the Bimodal/ logic which extends both Modal/ and Temporal/.

I noticed PR [#607](https://github.com/leanprover-community/mathlib4/pull/607) covers similar ground and think our approaches could converge:

- @chenson2018's review suggested consolidating operator files — the [`Foundations/Logic/Connectives.lean`](https://github.com/benbrastmckie/cslib/blob/feat/propositional-v2/Cslib/Foundations/Logic/Connectives.lean) is exactly that, one file for all connective typeclasses.
- The K/T/B/4/5/D proofs use explicit `simp only [Satisfies]` + `intro` rather than `grind`, avoiding the notation transparency issue @thomaskwaring flagged.

Would this direction work alongside or instead of [#607](https://github.com/leanprover-community/mathlib4/pull/607)'s modal components? Happy to coordinate.
