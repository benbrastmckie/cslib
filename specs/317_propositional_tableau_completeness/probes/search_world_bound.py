"""Search for a counterexample to `nextWorld <= phi0.complexity + 1`.

The `hnw` hypothesis of `intApplyRuleFull_outputs_subset` (Scheme.lean:1813) and the
label range of `intUniverse` (Scheme.lean:1575-1577, `List.range (complexity + 2)`)
both assert a LINEAR world bound. This script stresses it.

Family:  phi0 = ((A1->r1) & ... & (Am->rm))  ->  ((u1->v1) v ... v (uk->vk))
  with every Aj = (aj -> bj) itself `.imp`-shaped, all atoms distinct.

Mechanism under test (from handoffs/12_world-bound-decision.md): each T(Aj->rj)@1 is
`.pos`-signed, hence copied by propagatePersistence/applyAllTImpRules into every sibling
world; each copy BETA-resolves to a fresh F(Aj)@w, which re-fires world-creation.
So m shared implications x k sibling worlds should yield ~m*k creations against a
complexity of only 3m + 2k - 1.
"""

import sys, time
sys.setrecursionlimit(100000)
from int_tableau import (atom, imp, conj, disj, complexity, show, run,
                         is_intuitionistically_closed)

def right_nest(op, xs):
    f = xs[-1]
    for x in reversed(xs[:-1]):
        f = op(x, f)
    return f

def build(m, k):
    c = iter(range(10000))
    ants = []
    for _ in range(m):
        a, b, r = atom(next(c)), atom(next(c)), atom(next(c))
        ants.append(imp(imp(a, b), r))
    cons = []
    for _ in range(k):
        u, v = atom(next(c)), atom(next(c))
        cons.append(imp(u, v))
    return imp(right_nest(conj, ants), right_nest(disj, cons))

print(f"{'m':>3} {'k':>3} {'cplx':>5} {'bound':>6} {'creations':>10} {'maxNW':>6} "
      f"{'reuse':>6} {'steps':>7} {'|b|':>6} {'labels':>7} {'result':>11} {'VIOLATES?':>10}  secs")
print("-" * 110)

CASES = [(1, 3), (2, 2), (2, 3), (3, 3), (3, 4), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8)]

for (m, k) in CASES:
    phi = build(m, k)
    c = complexity(phi)
    bound = c + 1
    t0 = time.time()
    (kind, b), st = run(phi, step_cap=60000)
    dt = time.time() - t0
    labels = len(set(sf[2] for sf in b)) if b else 0
    blen = len(b) if b else 0
    viol = "YES" if st.max_next_world > bound else "no"
    if st.timed_out:
        viol = "(cap hit)"
    print(f"{m:>3} {k:>3} {c:>5} {bound:>6} {st.creations:>10} {st.max_next_world:>6} "
          f"{st.reuses:>6} {st.steps:>7} {blen:>6} {labels:>7} {str(kind):>11} {viol:>10}  {dt:6.1f}")
    sys.stdout.flush()
    if st.max_next_world > bound and not st.timed_out:
        print(f"\n*** COUNTEREXAMPLE at m={m},k={k} ***")
        print(f"    phi0 = {show(phi)}")
        print(f"    complexity = {c}, claimed bound nextWorld <= {bound}, "
              f"actual max nextWorld = {st.max_next_world}")
        break
