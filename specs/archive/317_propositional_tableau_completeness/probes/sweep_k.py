"""Focused sweep: m shared `.imp`-antecedent T-implications x k sibling F-implications.

Reports max nextWorld against the claimed linear bound `complexity + 1`
(`intApplyRuleFull_outputs_subset`'s `hnw`, Scheme.lean:1813).
"""
import sys, time
sys.setrecursionlimit(100000)
from int_tableau import atom, imp, conj, disj, complexity, show, run

def right_nest(op, xs):
    f = xs[-1]
    for x in reversed(xs[:-1]):
        f = op(x, f)
    return f

def build(m, k):
    c = iter(range(10000))
    ants = [imp(imp(atom(next(c)), atom(next(c))), atom(next(c))) for _ in range(m)]
    cons = [imp(atom(next(c)), atom(next(c))) for _ in range(k)]
    return imp(right_nest(conj, ants), right_nest(disj, cons))

cases = [(m, k) for m in (1, 2, 3) for k in (2, 3, 4, 5, 6)]
print(f"{'m':>2} {'k':>2} {'cplx':>5} {'bound':>6} {'creat':>6} {'maxNW':>6} {'reuse':>6} "
      f"{'steps':>7} {'|b|':>6} {'VIOL':>5}  secs", flush=True)
for (m, k) in cases:
    phi = build(m, k)
    c = complexity(phi)
    t0 = time.time()
    (kind, b), st = run(phi, step_cap=40000)
    dt = time.time() - t0
    flag = "(cap)" if st.timed_out else ("YES" if st.max_next_world > c + 1 else "no")
    print(f"{m:>2} {k:>2} {c:>5} {c+1:>6} {st.creations:>6} {st.max_next_world:>6} "
          f"{st.reuses:>6} {st.steps:>7} {len(b) if b else 0:>6} {flag:>5}  {dt:6.1f}",
          flush=True)
    if flag == "YES":
        print(f"\n*** COUNTEREXAMPLE m={m} k={k}: {show(phi)}", flush=True)
        print(f"    complexity={c}  claimed nextWorld <= {c+1}  actual max nextWorld="
              f"{st.max_next_world}", flush=True)
        break
