/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.Propositional.Defs

/-! # Operator Precedence Regression Guard

Guards the "Standing Invariant: Notation Collision Risk" documented in
`Cslib.Foundations.Logic.Connectives`: the `scoped` notations bound in the `Cslib.Logic`
namespace by `Operators.lean` (`→`, `∨`, `∧`, ...) must never collide with a core notation
at identical token + precedence + associativity. An *exact* collision turns every use of the
token into a parser `choice` node wherever the scoped notation is active; on a right-nested
chain of length `n` the elaborator then backtracks through Θ(2^n) alternative parses. The
walk is effectively unbounded by the heartbeat budget, because each failing alternative's
timeout is swallowed before the next alternative is tried — the failure mode is a silent,
catastrophic slowdown in *client* modules, not an error at the collision site.

The guard here is elaboration *speed* at the default heartbeat budget:

* The 24-`→` and 24-`∨` `Prop`-chain probes below elaborate flat (seconds) while the scoped
  precedences stay offset by one from core (`∧` 36 vs 35, `∨` 31 vs 30, `→` 26 vs 25). If an
  exact collision is reintroduced, they degrade to an exponential walk (tens of seconds and
  doubling per added connective) that ends in a heartbeat-timeout error.
* The two `rfl` grouping pins fix the formula-level parse trees, witnessing that the
  precedence offsets leave relative operator grouping — and hence formula semantics —
  unchanged.

Never add `set_option maxHeartbeats` in this file: a raised budget would mask exactly the
regression this file exists to catch.
-/

namespace Cslib.Logic.PL

/-! ## Performance probes

Flat-time with offset precedences; Θ(2^n) walk plus eventual timeout error if an exact
core-notation collision on `→` or `∨` regresses.
-/

-- 24-arrow `Prop` chain: elaborates in seconds iff the scoped `→` notation does not
-- exactly collide with core `→` in token + precedence + associativity.
example : True → True → True → True → True → True → True → True → True → True → True →
    True → True → True → True → True → True → True → True → True → True → True → True →
    True → True := by
  intros; trivial

-- 24-`∨` `Prop` chain: same guard for `∨`. Right-associated, so `Or.inl trivial`
-- closes the whole chain.
example : True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨
    True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨ True ∨
    True ∨ True := Or.inl trivial

/-! ## Grouping pins (semantics-unchanged gates)

These pin the formula-level parse trees produced by the scoped notation, so any precedence
change that alters relative grouping — rather than merely offsetting from core — fails loudly
here rather than silently changing formula semantics.
-/

-- `∧` binds tighter than `∨`, which binds tighter than `→`.
example (a b c : Proposition Nat) :
    (a ∧ b ∨ c → a) = HasImp.imp (HasOr.or (HasAnd.and a b) c) a := rfl

-- `→` on formulas is right-associative.
example (a b c : Proposition Nat) : (a → b → c) = a.imp (b.imp c) := rfl

end Cslib.Logic.PL
