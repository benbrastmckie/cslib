"""Randomized exhaustive-ish search over small formulas for counterexamples to:

  (A) the LINEAR world bound  `nextWorld <= phi0.complexity + 1`
      (= `hnw` of `intApplyRuleFull_outputs_subset`, Scheme.lean:1813, and the label range
       `List.range (complexity + 2)` baked into `intUniverse`, Scheme.lean:1575-1577)

  (B) atom-persistence of the produced branch
      (= the `IAtomPersist edges b` premise the two Completeness bridges need,
       Completeness.lean:133 / Minimal/Completeness.lean:125)

  (C) T-implication copy completeness on the produced branch
      (= the `sat_timp` premise truthLemma's T-imp case needs, Scheme.lean:599)

Usage: python3 -u random_search.py [n_samples] [max_complexity] [seed]
"""
import sys, random, time
sys.setrecursionlimit(100000)
from int_tableau import (atom, imp, conj, disj, BOT, complexity, show,
                         is_accessible, is_intuitionistically_closed, erase_dups)
from check_atom_persist import run_with_edges

N       = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
MAXC    = int(sys.argv[2]) if len(sys.argv) > 2 else 9
SEED    = int(sys.argv[3]) if len(sys.argv) > 3 else 20260726
NATOMS  = 3

rng = random.Random(SEED)

def rand_formula(depth):
    if depth == 0 or rng.random() < 0.30:
        return atom(rng.randrange(NATOMS)) if rng.random() < 0.9 else BOT
    op = rng.choice([imp, imp, imp, conj, disj])   # bias to imp (world-creating)
    return op(rand_formula(depth - 1), rand_formula(depth - 1))

def audit_one(phi):
    kind, b, edges, st = run_with_edges(phi, is_intuitionistically_closed, step_cap=25000)
    if kind != 'openBranch':
        return kind, st, None
    labels = erase_dups([sf[2] for sf in b])
    bset = set(b)
    atom_v, timp_v = [], []
    for sf in b:
        if sf[0] != 'T':
            continue
        for wp in labels:
            if wp != sf[2] and is_accessible(edges, sf[2], wp) and ('T', sf[1], wp) not in bset:
                if sf[1][0] == 'atom':
                    atom_v.append((sf, wp))
                elif sf[1][0] == 'imp':
                    timp_v.append((sf, wp))
    return kind, st, (atom_v, timp_v, edges, b, labels)

t0 = time.time()
seen = set()
worst_ratio, worst_phi = 0.0, None
n_open = n_closed = n_timeout = 0
hits_A = hits_B = hits_C = 0

for i in range(N):
    phi = rand_formula(rng.randrange(2, 5))
    c = complexity(phi)
    if c < 2 or c > MAXC or phi in seen:
        continue
    seen.add(phi)
    kind, st, aud = audit_one(phi)
    if kind == 'timeout':
        n_timeout += 1
        print(f"[TIMEOUT] cplx={c} steps>={st.steps} maxNW={st.max_next_world} {show(phi)}",
              flush=True)
        continue
    if kind == 'closed':
        n_closed += 1
    else:
        n_open += 1
    # (A) world bound -- applies whether or not the branch closes
    if st.max_next_world > c + 1:
        hits_A += 1
        print(f"\n*** (A) LINEAR WORLD BOUND VIOLATED ***", flush=True)
        print(f"    phi0 = {show(phi)}", flush=True)
        print(f"    complexity = {c}, claimed nextWorld <= {c+1}, "
              f"actual max nextWorld = {st.max_next_world}, creations = {st.creations}",
              flush=True)
        break
    ratio = st.max_next_world / (c + 1)
    if ratio > worst_ratio:
        worst_ratio, worst_phi = ratio, (phi, c, st.max_next_world, st.creations, kind)
    if aud is None:
        continue
    atom_v, timp_v, edges, b, labels = aud
    if atom_v:
        hits_B += 1
        print(f"\n*** (B) ATOM-PERSISTENCE VIOLATED ***", flush=True)
        print(f"    phi0 = {show(phi)}  complexity={c}", flush=True)
        print(f"    edges={edges}  labels={sorted(labels)}", flush=True)
        for (sf, wp) in atom_v[:5]:
            print(f"    T({show(sf[1])})@{sf[2]} present, accessible {sf[2]}->{wp}, "
                  f"but T({show(sf[1])})@{wp} ABSENT", flush=True)
        break
    if timp_v:
        hits_C += 1
        print(f"\n*** (C) T-IMPLICATION COPY INCOMPLETE ***", flush=True)
        print(f"    phi0 = {show(phi)}  complexity={c}", flush=True)
        print(f"    edges={edges}  labels={sorted(labels)}", flush=True)
        for (sf, wp) in timp_v[:5]:
            print(f"    T({show(sf[1])})@{sf[2]} present, accessible {sf[2]}->{wp}, "
                  f"but T({show(sf[1])})@{wp} ABSENT", flush=True)
        break

print(f"\n--- summary ({time.time()-t0:.1f}s) ---", flush=True)
print(f"distinct formulas tested : {len(seen)}", flush=True)
print(f"open / closed / timeout  : {n_open} / {n_closed} / {n_timeout}", flush=True)
print(f"violations  A(bound) B(atom-persist) C(timp-copy) : "
      f"{hits_A} / {hits_B} / {hits_C}", flush=True)
if worst_phi:
    phi, c, mnw, cr, kind = worst_phi
    print(f"tightest world-bound case: maxNW={mnw} vs bound={c+1} "
          f"(ratio {worst_ratio:.3f}), creations={cr}, {kind}", flush=True)
    print(f"    {show(phi)}", flush=True)
