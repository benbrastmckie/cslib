"""Does the tableau's OWN output branch satisfy atom-persistence (upward closure)?

`intuitionisticTableau_complete` (Completeness.lean:133) and `minimalTableau_complete`
(Minimal/Completeness.lean:125) must bridge `IValid phi` to
  forall edges b, IForces (intExtractValuation b) (fun _ => False) 0 phi
at the frame `intAccessPreorder edges`. `IValid` only supplies forcing for UPWARD-CLOSED
valuations, so the bridge needs `intExtractValuation b` to be upward-closed along
`isAccessible edges`, i.e.

  IAtomPersist:  T(atom p)@w in b  and  isAccessible edges w w'  ==>  T(atom p)@w' in b

The phase-0 spike (handoffs/11_phase0-spike-decisions.md, Question (b)) concluded the
bridge must be narrowed by adding this as a hypothesis. That narrowing is only viable if
the property actually HOLDS of the branch/edges pair the expansion produces.

This script checks exactly that on the branches the real algorithm returns.
It also checks the analogous property for compound T-formulas (needed by sat_timp's
"every accessible world carries its own T(phi->psi) copy" premise) and whether the
edge endpoints all appear as labels on the branch.
"""
import sys
sys.setrecursionlimit(100000)
from int_tableau import (atom, imp, conj, disj, BOT, complexity, show, run,
                         is_accessible, is_intuitionistically_closed, is_minimally_closed,
                         erase_dups, Stats, apply_persistence_fixpoint,
                         int_expand_branches)

# We need the edge list that accompanies the returned open branch. int_expand_branches
# returns only the branch, mirroring Lean. Re-run with an instrumented copy that also
# reports the edges active at the `openBranch` leaf.
import int_tableau as IT

def run_with_edges(phi, closure_pred=is_intuitionistically_closed, step_cap=60000, fuel=None):
    """Same loop as int_expand_branches but returns (kind, branch, edges)."""
    stats = Stats()
    fuel = IT.int_fuel(phi) if fuel is None else fuel
    branches, expanded_sets = [[('F', phi, 0)]], [[]]
    next_worlds, edge_sets = [1], [[]]
    while True:
        if stats.steps >= step_cap:
            return ('timeout', None, None, stats)
        if fuel == 0:
            for b, ed in zip(branches, edge_sets):
                if not closure_pred(b):
                    return ('openBranch', b, ed, stats)
            return ('closed', None, None, stats)
        fuel_prime = fuel - 1
        pending = list(zip(branches, expanded_sets, next_worlds, edge_sets))
        done_b, done_e, done_nw, done_ed = [], [], [], []
        result = None
        idx = 0
        while idx < len(pending):
            b, e, nw, edges = pending[idx]
            b_pers = apply_persistence_fixpoint(b, edges, fuel)
            if closure_pred(b_pers):
                done_b.append(b_pers); done_e.append(e)
                done_nw.append(nw); done_ed.append(edges); idx += 1; continue
            step = IT.int_step_branch(b_pers, e, nw)
            if step is None:
                return ('openBranch', b_pers, edges, stats)
            (kind, payload, nwp, new_edge), new_exp = step
            rest = pending[idx + 1:]
            rb = [x[0] for x in rest]; re_ = [x[1] for x in rest]
            rnw = [x[2] for x in rest]; red = [x[3] for x in rest]
            if kind == IT.LINEAR and new_edge is None:
                result = (done_b + [IT.extend_many(b_pers, payload)] + rb,
                          done_e + [new_exp] + re_, done_nw + [nwp] + rnw,
                          done_ed + [edges] + red)
            elif kind == IT.LINEAR:
                wit = IT.int_fimp_reuse_witness(b_pers, edges, payload, new_edge)
                if wit is not None:
                    stats.reuses += 1
                    result = (done_b + [b_pers] + rb, done_e + [new_exp] + re_,
                              done_nw + [nw] + rnw, done_ed + [edges] + red)
                else:
                    stats.creations += 1
                    stats.max_next_world = max(stats.max_next_world, nwp)
                    result = (done_b + [IT.extend_many(b_pers, payload)] + rb,
                              done_e + [new_exp] + re_, done_nw + [nwp] + rnw,
                              done_ed + [edges + [new_edge]] + red)
            else:
                result = (done_b + [IT.extend_many(b_pers, br) for br in payload] + rb,
                          done_e + [new_exp for _ in payload] + re_,
                          done_nw + [nwp for _ in payload] + rnw,
                          done_ed + [edges for _ in payload] + red)
            break
        else:
            return ('closed', None, None, stats)
        branches, expanded_sets, next_worlds, edge_sets = result
        fuel = fuel_prime
        stats.steps += 1


def audit(name, phi, closure_pred=is_intuitionistically_closed):
    kind, b, edges, st = run_with_edges(phi, closure_pred)
    print(f"\n=== {name} :  {show(phi)}")
    print(f"    complexity={complexity(phi)}  result={kind}  "
          f"creations={st.creations} maxNW={st.max_next_world} reuses={st.reuses}")
    if kind != 'openBranch':
        print("    (no open branch; nothing to audit)")
        return None
    labels = erase_dups([sf[2] for sf in b])
    bset = set(b)
    print(f"    |b|={len(b)}  labels={sorted(labels)}  edges={edges}")

    # (1) atom persistence
    atom_viol = []
    for sf in b:
        if sf[0] == 'T' and sf[1][0] == 'atom':
            for wp in labels:
                if is_accessible(edges, sf[2], wp) and ('T', sf[1], wp) not in bset:
                    atom_viol.append((show(sf[1]), sf[2], wp))
    # (2) general T-formula persistence
    all_viol = []
    for sf in b:
        if sf[0] == 'T':
            for wp in labels:
                if is_accessible(edges, sf[2], wp) and ('T', sf[1], wp) not in bset:
                    all_viol.append((show(sf[1]), sf[2], wp))
    # (3) T-implication copy completeness (the sat_timp premise)
    timp_viol = []
    for sf in b:
        if sf[0] == 'T' and sf[1][0] == 'imp':
            for wp in labels:
                if is_accessible(edges, sf[2], wp) and ('T', sf[1], wp) not in bset:
                    timp_viol.append((show(sf[1]), sf[2], wp))
    # (4) edge endpoints appear as labels on b
    ep_viol = [e for e in edges if e[0] not in labels or e[1] not in labels]

    def rep(tag, v):
        print(f"    {tag:<34} {'OK' if not v else 'VIOLATED (' + str(len(v)) + ')'}")
        for x in v[:6]:
            print(f"        T({x[0]})@{x[1]} but not @{x[2]} (accessible)")
    rep("IAtomPersist (atoms upward-closed)", atom_viol)
    rep("all T-formulas upward-closed", all_viol)
    rep("T-implication copies complete", timp_viol)
    print(f"    {'edge endpoints are branch labels':<34} "
          f"{'OK' if not ep_viol else 'VIOLATED ' + str(ep_viol)}")
    return atom_viol, all_viol, timp_viol, ep_viol


if __name__ == '__main__':
    p, q, r, s, t = (atom(i) for i in range(5))
    u1, v1, u2, v2, u3, v3 = (atom(i) for i in range(5, 11))

    # The v12 counterexample.
    A1 = imp(p, q)
    phi_v12 = imp(conj(imp(A1, r), imp(s, t)), disj(imp(u1, v1), disj(imp(u2, v2), imp(u3, v3))))
    audit("v12 counterexample", phi_v12)

    # Simplest world-creating formula with an atom that arrives at a parent after a child exists.
    # F( (p -> q) -> ((r -> s) -> p) )   : creates w1 with T(p->q),F((r->s)->p);
    #                                      then w2 with T(r->s),F(p); T(p->q) copied down.
    audit("nested imp", imp(imp(p, q), imp(imp(r, s), p)))

    # Kreisel-Putnam-ish shape / atom introduced at a parent late.
    audit("late atom at parent", imp(imp(p, disj(q, r)), disj(imp(p, q), imp(p, r))))

    # and-decomposition producing an atom at world 0 after world 1 exists
    audit("conj after creation", imp(conj(imp(p, q), r), imp(s, conj(r, t))))

    # minimal-logic variant of the same
    audit("v12 (minimal closure)", phi_v12, is_minimally_closed)
