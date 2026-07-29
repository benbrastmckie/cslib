"""Faithful Python port of Cslib's intuitionistic tableau expansion loop.

Ported line-by-line from (commit-pinned):
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Rules.lean
  Cslib/Logics/Propositional/Tableau/Intuitionistic/Expansion.lean
  Cslib/Foundations/Logic/Tableau/Branch.lean        (extendMany, findContradiction)
  Cslib/Foundations/Logic/Tableau/ClosureCondition.lean (IntuitionisticClosure)

Purpose: settle whether `nextWorld <= phi0.complexity + 1` (the `hnw` hypothesis of
`intApplyRuleFull_outputs_subset`, Scheme.lean) actually holds, without the `#eval`
sandbox timeouts reported in handoffs/12_world-bound-decision.md.

FIDELITY NOTE: validated against the Lean-computed data point in
handoffs/12_world-bound-decision.md (the complexity-10 three-sibling counterexample:
branch length 77, 9 distinct labels 0..8) -- see `validate()`.

Representations:
  formula : ('atom', n) | ('bot',) | ('imp', a, b) | ('and', a, b) | ('or', a, b)
  sf      : (sign, formula, label)   with sign in {'T','F'}   [T = .pos, F = .neg]
  branch  : list of sf   (order-significant; extendMany PREPENDS)
  edges   : list of (child, parent)
"""

import sys
from itertools import count

# ---------------------------------------------------------------- formulas

def atom(n): return ('atom', n)
BOT = ('bot',)
def imp(a, b): return ('imp', a, b)
def conj(a, b): return ('and', a, b)
def disj(a, b): return ('or', a, b)

def complexity(f):
    # Proposition.complexity, Subformula.lean:193-198
    if f[0] in ('atom', 'bot'):
        return 0
    return 1 + complexity(f[1]) + complexity(f[2])

def show(f):
    if f[0] == 'atom': return f"p{f[1]}"
    if f[0] == 'bot': return "_|_"
    op = {'imp': '->', 'and': '&', 'or': 'v'}[f[0]]
    return f"({show(f[1])}{op}{show(f[2])})"

# ---------------------------------------------------------------- erase_dups

def erase_dups(xs):
    """List.eraseDups: keeps FIRST occurrence, preserves order."""
    seen, out = set(), []
    for x in xs:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out

# ---------------------------------------------------------------- accessibility

def is_accessible(edges, w, wp):
    """Rules.lean:87-102. DFS over reverse edge graph, fuel = len(edges)."""
    if w == wp:
        return True

    def go(current, fuel):
        if fuel == 0:
            return False
        children = [child for (child, parent) in edges if parent == current]
        for child in children:
            if child == wp:
                return True
            if go(child, fuel - 1):
                return True
        return False

    return go(w, len(edges))

# ---------------------------------------------------------------- persistence

def pos_formulas_at(b, w):
    """Rules.lean:126-128 -- posFormulasAt."""
    return [sf[1] for sf in b if sf[0] == 'T' and sf[2] == w]

def propagate_persistence(b, from_w, to_w):
    """Rules.lean:139-141."""
    return [('T', f, to_w) for f in pos_formulas_at(b, from_w)]

def int_timp_rule(phi, psi, w, edges, b):
    """Rules.lean:174-186."""
    labels = erase_dups([sf[2] for sf in b])
    accessible = [x for x in labels if is_accessible(edges, w, x)]
    bset = set(b)
    out = []
    for wp in accessible:
        if ('T', phi, wp) in bset:
            if ('T', psi, wp) in bset:
                pass
            else:
                out.append(('T', psi, wp))
    return out

def apply_all_timp_rules(b, edges):
    """Expansion.lean:129-147."""
    labels = erase_dups([sf[2] for sf in b])
    bset = set(b)
    new_forms = []
    for sf in b:
        sign, f, l = sf
        if sign == 'T' and f[0] == 'imp':
            phi, psi = f[1], f[2]
            to_add = int_timp_rule(phi, psi, l, edges, b)
            accessible = [x for x in labels if is_accessible(edges, l, x)]
            copies = [('T', f, wp) for wp in accessible if ('T', f, wp) not in bset]
            combined = to_add + copies
            if combined:
                new_forms.append(combined)
    flat = [x for grp in new_forms for x in grp]
    return b + flat

def apply_persistence_fixpoint(b, edges, fuel):
    """Expansion.lean:153-159."""
    while fuel > 0:
        bp = apply_all_timp_rules(b, edges)
        if len(bp) == len(b):
            return b
        b = bp
        fuel -= 1
    return b

# ---------------------------------------------------------------- rules

LINEAR, BRANCHING, NOTAPPLICABLE = 'linear', 'branching', 'na'

def int_fimp_rule(phi, psi, w, next_world, b):
    """Rules.lean:154-159. Returns (newForms, nextWorld', edge)."""
    wp = next_world
    new_forms = [('T', phi, wp), ('F', psi, wp)] + propagate_persistence(b, w, wp)
    return new_forms, next_world + 1, (wp, w)

def int_apply_rule_full(sf, next_world, b):
    """Rules.lean:245-278. Returns (kind, payload, nextWorld', edge)."""
    sign, f, l = sf
    if sign == 'T' and f[0] == 'and':
        return (LINEAR, [('T', f[1], l), ('T', f[2], l)], next_world, None)
    if sign == 'F' and f[0] == 'and':
        return (BRANCHING, [[('F', f[1], l)], [('F', f[2], l)]], next_world, None)
    if sign == 'T' and f[0] == 'or':
        return (BRANCHING, [[('T', f[1], l)], [('T', f[2], l)]], next_world, None)
    if sign == 'F' and f[0] == 'or':
        return (LINEAR, [('F', f[1], l), ('F', f[2], l)], next_world, None)
    if sign == 'F' and f[0] == 'imp':
        nf, nw, e = int_fimp_rule(f[1], f[2], l, next_world, b)
        return (LINEAR, nf, nw, e)
    if sign == 'T' and f[0] == 'imp':
        return (BRANCHING, [[('F', f[1], l)], [('T', f[2], l)]], next_world, None)
    return (NOTAPPLICABLE, None, next_world, None)

def int_step_branch(b, expanded, next_world):
    """Expansion.lean:170-177. Returns (result, newExpanded) or None."""
    for sf in b:
        if sf in expanded:
            continue
        r = int_apply_rule_full(sf, next_world, b)
        if r[0] != NOTAPPLICABLE:
            return r, expanded + [sf]
    return None

def int_fimp_reuse_witness(b_pers, edges, new_forms, new_edge):
    """Expansion.lean:283-311."""
    w = new_edge[1]
    psi = None
    for sf in new_forms:
        if sf[0] == 'F':
            psi = sf[1]
            break
    if psi is None:
        return None
    sfor = [sf[1] for sf in new_forms if sf[0] == 'T']
    candidates = erase_dups([sf[2] for sf in b_pers])
    for x in candidates:
        forced = set(pos_formulas_at(b_pers, x))
        if (is_accessible(edges, w, x)
                and w <= x
                and all(s in forced for s in sfor)
                and psi not in forced
                and any(y[0] == 'F' and y[1] == psi and y[2] == x for y in b_pers)):
            return x
    return None

# ---------------------------------------------------------------- closure

def has_contradiction(b):
    """Branch.lean:90-101."""
    bset = set(b)
    for sf in b:
        if sf[0] == 'T' and ('F', sf[1], sf[2]) in bset:
            return True
    return False

def is_intuitionistically_closed(b):
    """Expansion.lean:92-95: T(bot) at any label OR complementary pair."""
    if any(sf[0] == 'T' and sf[1] == BOT for sf in b):
        return True
    return has_contradiction(b)

def is_minimally_closed(b):
    return has_contradiction(b)

# ---------------------------------------------------------------- expansion loop

class Stats:
    def __init__(self):
        self.steps = 0
        self.max_next_world = 0
        self.creations = 0
        self.reuses = 0
        self.timed_out = False

def extend_many(b, sfs):
    """Branch.extendMany b sfs = sfs ++ b  (Branch.lean:62) -- PREPENDS."""
    return sfs + b

def int_expand_branches(branches, expanded_sets, next_worlds, edge_sets, fuel,
                        closure_pred, stats, step_cap):
    """Expansion.lean:360-450, rewritten as a trampoline (Lean's recursion is
    a tail call into intExpandBranches with fuel-1)."""
    while True:
        if stats.steps >= step_cap:
            stats.timed_out = True
            return ('timeout', None)
        if fuel == 0:
            for b in branches:
                if not closure_pred(b):
                    return ('openBranch', b)
            return ('closed', None)

        fuel_prime = fuel - 1
        # inner `go`
        pending = list(zip(branches, expanded_sets, next_worlds, edge_sets))
        done_b, done_e, done_nw, done_ed = [], [], [], []
        result = None
        idx = 0
        while idx < len(pending):
            b, e, nw, edges = pending[idx]
            b_pers = apply_persistence_fixpoint(b, edges, fuel)
            if closure_pred(b_pers):
                done_b.append(b_pers); done_e.append(e)
                done_nw.append(nw); done_ed.append(edges)
                idx += 1
                continue
            step = int_step_branch(b_pers, e, nw)
            if step is None:
                return ('openBranch', b_pers)
            (kind, payload, nwp, new_edge), new_exp = step
            rest = pending[idx + 1:]
            rest_b = [x[0] for x in rest]; rest_e = [x[1] for x in rest]
            rest_nw = [x[2] for x in rest]; rest_ed = [x[3] for x in rest]
            if kind == LINEAR and new_edge is None:
                result = (done_b + [extend_many(b_pers, payload)] + rest_b,
                          done_e + [new_exp] + rest_e,
                          done_nw + [nwp] + rest_nw,
                          done_ed + [edges] + rest_ed)
            elif kind == LINEAR:
                wit = int_fimp_reuse_witness(b_pers, edges, payload, new_edge)
                if wit is not None:
                    stats.reuses += 1
                    result = (done_b + [b_pers] + rest_b,
                              done_e + [new_exp] + rest_e,
                              done_nw + [nw] + rest_nw,
                              done_ed + [edges] + rest_ed)
                else:
                    stats.creations += 1
                    stats.max_next_world = max(stats.max_next_world, nwp)
                    result = (done_b + [extend_many(b_pers, payload)] + rest_b,
                              done_e + [new_exp] + rest_e,
                              done_nw + [nwp] + rest_nw,
                              done_ed + [edges + [new_edge]] + rest_ed)
            else:  # BRANCHING
                result = (done_b + [extend_many(b_pers, br) for br in payload] + rest_b,
                          done_e + [new_exp for _ in payload] + rest_e,
                          done_nw + [nwp for _ in payload] + rest_nw,
                          done_ed + [edges for _ in payload] + rest_ed)
            break
        else:
            return ('closed', None)

        branches, expanded_sets, next_worlds, edge_sets = result
        fuel = fuel_prime
        stats.steps += 1

def int_fuel(phi):
    c = complexity(phi)
    return 3 ** (4 * (2 * c + 1) * (c + 2))

def run(phi, closure_pred=is_intuitionistically_closed, step_cap=200000, fuel=None):
    """Expansion.lean:500-503 -- intuitionisticTableau."""
    stats = Stats()
    if fuel is None:
        fuel = int_fuel(phi)
        # int_fuel is astronomically large; step_cap is the real limiter.
    res = int_expand_branches([[('F', phi, 0)]], [[]], [1], [[]],
                              fuel, closure_pred, stats, step_cap)
    return res, stats


# ---------------------------------------------------------------- validation

def validate():
    """Reproduce the Lean-verified data point from handoffs/12_world-bound-decision.md."""
    p, q, r, s, t = atom(0), atom(1), atom(2), atom(3), atom(4)
    u1, v1, u2, v2, u3, v3 = (atom(i) for i in range(5, 11))
    A1 = imp(p, q)
    ante = conj(imp(A1, r), imp(s, t))
    cons_ = disj(imp(u1, v1), disj(imp(u2, v2), imp(u3, v3)))
    phi0 = imp(ante, cons_)
    (kind, b), st = run(phi0)
    labels = sorted(set(sf[2] for sf in b)) if b else []
    print(f"[validate] complexity(phi0) = {complexity(phi0)}   (Lean: 10)")
    print(f"[validate] result           = {kind}              (Lean: openBranch)")
    print(f"[validate] branch length    = {len(b) if b else '-'}   (Lean: 77)")
    print(f"[validate] distinct labels  = {len(labels)} {labels}  (Lean: 9, 0..8)")
    neg_imps = [(show(sf[1]), sf[2]) for sf in b if sf[0] == 'F' and sf[1][0] == 'imp']
    print(f"[validate] F-signed .imp entries ({len(neg_imps)}):")
    for x in neg_imps:
        print("            ", x)
    ok = (complexity(phi0) == 10 and kind == 'openBranch'
          and len(b) == 77 and len(labels) == 9)
    print(f"[validate] MATCHES LEAN: {ok}")
    return ok


if __name__ == '__main__':
    validate()
