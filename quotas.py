#!/usr/bin/env python3
"""Exact color quotas on paths: joint versus separate filtering.

Companion code for "Exact Color Quotas on Paths and Cycles" (L. Dong, Z. Li).
Joint filtering is domain consistency for the conjunction of the adjacency rule
and exact quotas, computed with the constant-time support tests of Algorithm 1
(Theorem 7).  Separate filtering is the fixed point of arc consistency on the
chain of disequalities (equal to domain consistency for regular on a path) and
Regin's domain consistency for gcc.  Pure Python, no dependencies.

Usage: python quotas.py validate|root|infeasible|search|timing|all [--seed S]
Every experiment reseeds the generator with S, so `all` reproduces the
separate runs exactly.
"""
import argparse
import itertools
import random
import statistics
import sys
import time
from collections import deque
from functools import lru_cache

NEG = float('-inf')


# ---------------------------------------------------------------- instances

def gaps_of(pre):
    """Maximal runs of free vertices as (start, length, left label, right label)."""
    n = len(pre)
    out = []
    i = 0
    while i < n:
        if pre[i] is not None:
            i += 1
            continue
        j = i
        while j < n and pre[j] is None:
            j += 1
        out.append((i, j - i, pre[i - 1] if i > 0 else None, pre[j] if j < n else None))
        i = j
    return out


def valid_input(pre, r):
    if any(q < 0 for q in r):
        return False
    if any(pre[i] is not None and pre[i] == pre[i + 1] for i in range(len(pre) - 1)):
        return False
    return sum(r) == sum(1 for c in pre if c is None)


def generate(n, k, p, skew, delta, rng):
    """Random proper coloring, precolor each vertex with probability p, take the
    free counts as quotas, then move `delta` quota units between random colors.
    With probability `skew` the coloring uses color 0 whenever it is allowed."""
    col = []
    for i in range(n):
        allowed = [c for c in range(k) if not col or c != col[-1]] or list(range(k))
        if 0 in allowed and rng.random() < skew:
            col.append(0)
        else:
            col.append(rng.choice(allowed))
    pre = [c if rng.random() < p else None for c in col]
    r = [0] * k
    for c, q in zip(col, pre):
        if q is None:
            r[c] += 1
    for _ in range(delta):
        pos = [c for c in range(k) if r[c] > 0]
        if not pos or k < 2:
            break
        c = rng.choice(pos)
        d = rng.choice([x for x in range(k) if x != c])
        r[c] -= 1
        r[d] += 1
    return pre, r


# ------------------------------------------------- cut statistics (Thm 2)

def contrib(m, a, b):
    """Contribution of one gap of length m >= 1 to W, B, D, H."""
    B, D, H = {}, {}, {}
    if m % 2 == 0:
        if a is not None and a == b:
            B[a] = 1
    else:
        for c in {a, b}:
            if c is not None:
                D[c] = 1
        if a is not None and b is not None and a != b:
            H[(min(a, b), max(a, b))] = 1
    return (m + 1) // 2, B, D, H


def cut_stats(gaps, k):
    W = 0
    B = [0] * k
    D = [0] * k
    H = {}
    for (_, m, a, b) in gaps:
        w, cb, cd, ch = contrib(m, a, b)
        W += w
        for c, v in cb.items():
            B[c] += v
        for c, v in cd.items():
            D[c] += v
        for e, v in ch.items():
            H[e] = H.get(e, 0) + v
    return W, B, D, H


def feasible(pre, k, r):
    """Singleton and pair tests of Theorem 2."""
    if not valid_input(pre, r):
        return False
    W, B, D, H = cut_stats(gaps_of(pre), k)
    N = sum(r)
    if any(r[c] + B[c] + D[c] > W for c in range(k)):
        return False
    if k >= 2:
        S = [r[c] + B[c] for c in range(k)]
        top = sorted(S, reverse=True)
        if top[0] + top[1] > N:
            return False
        for (c, d), h in H.items():
            if S[c] + S[d] + h > N:
                return False
    return True


# ------------------------------------- joint domain consistency (Thm 7)

def _build_tree(edges, S, U=frozenset(), depth=0):
    best, score = None, NEG
    for (c, d, h) in edges:
        if c in U or d in U:
            continue
        s = S[c] + S[d] + h
        if s > score:
            best, score = (c, d), s
    node = {'edge': best, 'score': score, 'kids': {}}
    if best is not None and depth < 3:
        for e in best:
            node['kids'][e] = _build_tree(edges, S, U | {e}, depth + 1)
    return node


def _query_tree(node, T):
    while True:
        e = node['edge']
        if e is None:
            return NEG
        c, d = e
        if c not in T and d not in T:
            return node['score']
        node = node['kids'][c if c in T else d]


def supports_fast(pre, k, r, stats=None):
    """Return the set of supported (vertex, color) pairs at free vertices, or None
    if the instance is infeasible.  Each candidate test takes O(1) time."""
    if not feasible(pre, k, r):
        return None
    gaps = gaps_of(pre)
    W, B, D, H = cut_stats(gaps, k)
    N = sum(r)
    Q = [r[c] + B[c] + D[c] for c in range(k)]
    S = [r[c] + B[c] for c in range(k)]
    topQ = sorted(range(k), key=lambda c: -Q[c])[:4]
    topS = sorted(range(k), key=lambda c: -S[c])[:5]
    edges = [(c, d, h) for (c, d), h in H.items()]
    nbr = [[] for _ in range(k)]
    for (c, d, h) in edges:
        nbr[c].append((S[d] + h, d))
        nbr[d].append((S[c] + h, c))
    for c in range(k):
        nbr[c] = sorted(nbr[c], reverse=True)[:3]
    tree = _build_tree(edges, S)
    tests = 0
    sup = set()
    for (st, m, a, b) in gaps:
        w0, b0, d0, h0 = contrib(m, a, b)
        for x in range(k):
            if r[x] == 0:
                continue
            for par in (1, 2):
                i = par
                if i == 1 and x == a:
                    i += 2
                if i > m or (i == m and x == b):
                    continue
                tests += 1
                parts = []
                if i - 1 > 0:
                    parts.append(contrib(i - 1, a, x))
                if m - i > 0:
                    parts.append(contrib(m - i, x, b))
                T = {c for c in (a, b, x) if c is not None}
                W2 = W - w0 + sum(pt[0] for pt in parts)
                N2 = N - 1
                Q2, S2 = {}, {}
                for c in T:
                    rc = r[c] - (1 if c == x else 0)
                    bc = B[c] - b0.get(c, 0) + sum(pt[1].get(c, 0) for pt in parts)
                    dc = D[c] - d0.get(c, 0) + sum(pt[2].get(c, 0) for pt in parts)
                    Q2[c] = rc + bc + dc
                    S2[c] = rc + bc
                qmax = max(Q2.values())
                for c in topQ:
                    if c not in T:
                        qmax = max(qmax, Q[c])
                        break
                ok = qmax <= W2
                if ok and k >= 2:
                    cand = sorted(list(S2.values()) + [S[c] for c in topS if c not in T][:2],
                                  reverse=True)
                    pm = cand[0] + cand[1]
                    pm = max(pm, _query_tree(tree, T))
                    for c in T:
                        for (sc, d) in nbr[c]:
                            if d not in T:
                                pm = max(pm, S2[c] + sc)
                                break
                    for c, d in itertools.combinations(sorted(T), 2):
                        h2 = H.get((c, d), 0) - h0.get((c, d), 0) + \
                            sum(pt[3].get((c, d), 0) for pt in parts)
                        if h2 > 0:
                            pm = max(pm, S2[c] + S2[d] + h2)
                    ok = pm <= N2
                if ok:
                    for pos in range(par, m + 1, 2):
                        if (pos == 1 and x == a) or (pos == m and x == b):
                            continue
                        sup.add((st + pos - 1, x))
    if stats is not None:
        stats['tests'] = tests
    return sup


def supports_naive(pre, k, r):
    """Reference: fix every free vertex to every color and rerun Theorem 2."""
    if not feasible(pre, k, r):
        return None
    sup = set()
    for v, c0 in enumerate(pre):
        if c0 is not None:
            continue
        for x in range(k):
            if r[x] == 0:
                continue
            p2 = list(pre)
            p2[v] = x
            r2 = list(r)
            r2[x] -= 1
            if feasible(p2, k, r2):
                sup.add((v, x))
    return sup


def supports_brute(pre, k, r):
    """Exhaustive reference for small instances."""
    n = len(pre)
    if not valid_input(pre, r):
        return None

    def feas(fv, fc):
        @lru_cache(maxsize=None)
        def f(i, last, rem):
            if i == n:
                return not any(rem)
            if pre[i] is not None:
                return pre[i] != last and f(i + 1, pre[i], rem)
            for c in range(k):
                if c == last or rem[c] == 0 or (i == fv and c != fc):
                    continue
                rl = list(rem)
                rl[c] -= 1
                if f(i + 1, c, tuple(rl)):
                    return True
            return False
        return f(0, None, tuple(r))

    if not feas(-1, -1):
        return None
    return {(v, c) for v in range(n) if pre[v] is None for c in range(k) if feas(v, c)}


# ------------------------- separate filtering: regular (AC on chain) + gcc

def ac_neq(dom):
    """Arc consistency on the chain of disequalities.  The constraint graph is a
    path, so this equals domain consistency of the regular constraint."""
    n = len(dom)
    q = deque(i for i in range(n) if len(dom[i]) == 1)
    removed = 0
    while q:
        i = q.popleft()
        (c,) = dom[i]
        for j in (i - 1, i + 1):
            if 0 <= j < n and c in dom[j]:
                dom[j].discard(c)
                removed += 1
                if not dom[j]:
                    return None
                if len(dom[j]) == 1:
                    q.append(j)
    return removed


def _scc(nn, adj):
    index = [-1] * nn
    low = [0] * nn
    onst = [False] * nn
    st = []
    comp = [-1] * nn
    idx = 0
    cc = 0
    for s in range(nn):
        if index[s] != -1:
            continue
        index[s] = low[s] = idx
        idx += 1
        st.append(s)
        onst[s] = True
        stack = [(s, 0)]
        while stack:
            v, pi = stack[-1]
            if pi < len(adj[v]):
                stack[-1] = (v, pi + 1)
                w = adj[v][pi]
                if index[w] == -1:
                    index[w] = low[w] = idx
                    idx += 1
                    st.append(w)
                    onst[w] = True
                    stack.append((w, 0))
                elif onst[w]:
                    low[v] = min(low[v], index[w])
            else:
                stack.pop()
                if stack:
                    u = stack[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    while True:
                        w = st.pop()
                        onst[w] = False
                        comp[w] = cc
                        if w == v:
                            break
                    cc += 1
    return comp


def gcc_dc(dom, free, k, r, match):
    """Regin's domain consistency for gcc with exact counts r on the free vertices.
    `match` (vertex -> color) is reused as a warm start.  Returns the number of
    removed values or None on failure."""
    load = [0] * k
    holders = [set() for _ in range(k)]
    for v in free:
        c = match.get(v)
        if c is not None and (c not in dom[v] or load[c] >= r[c]):
            del match[v]
            c = None
        if c is not None:
            load[c] += 1
            holders[c].add(v)
    for v in free:
        if v not in match:
            for c in dom[v]:
                if load[c] < r[c]:
                    match[v] = c
                    load[c] += 1
                    holders[c].add(v)
                    break
    for v in free:
        if v in match:
            continue
        par_val = {}
        par_var = {v: None}
        queue = [v]
        qi = 0
        end = None
        while qi < len(queue) and end is None:
            w = queue[qi]
            qi += 1
            for c in dom[w]:
                if c in par_val:
                    continue
                par_val[c] = w
                if load[c] < r[c]:
                    end = c
                    break
                for y in holders[c]:
                    if y not in par_var:
                        par_var[y] = c
                        queue.append(y)
        if end is None:
            return None
        c = end
        load[c] += 1
        while True:
            w = par_val[c]
            prev = match.get(w)
            if prev is not None:
                holders[prev].discard(w)
            match[w] = c
            holders[c].add(w)
            if w == v:
                break
            c = prev
    F = len(free)
    pos = {v: i for i, v in enumerate(free)}
    adj = [[] for _ in range(F + k)]
    for i, v in enumerate(free):
        mv = match[v]
        adj[i] = [F + c for c in dom[v] if c != mv]
    for c in range(k):
        adj[F + c] = [pos[v] for v in holders[c]]
    comp = _scc(F + k, adj)
    removed = 0
    for i, v in enumerate(free):
        mv = match[v]
        bad = [c for c in dom[v] if c != mv and comp[i] != comp[F + c]]
        for c in bad:
            dom[v].discard(c)
        removed += len(bad)
    return removed


def propagate_separate(dom, free, k, r, match):
    """Fixed point of the two propagators.  Returns False on a wipe-out."""
    while True:
        a = ac_neq(dom)
        if a is None:
            return False
        g = gcc_dc(dom, free, k, r, match)
        if g is None:
            return False
        if g == 0:
            return True


def separate_filter(pre, k, r):
    if not valid_input(pre, r):
        return None
    dom = [{c} if c is not None else set(range(k)) for c in pre]
    free = [v for v, c in enumerate(pre) if c is None]
    match = {}
    if not propagate_separate(dom, free, k, r, match):
        return None
    return dom


# ------------------------------------------------------------------ search

class Budget(Exception):
    pass


def search_separate(pre, k, r, limit):
    """DFS with separate propagation, leftmost variable, smallest value first.
    Returns (outcome, nodes) with outcome in {'sat', 'unsat', 'limit'}."""
    nodes = [0]
    if not valid_input(pre, r):
        return 'unsat', 0
    free = [v for v, c in enumerate(pre) if c is None]
    dom = [{c} if c is not None else set(range(k)) for c in pre]
    match = {}
    nodes[0] += 1
    if not propagate_separate(dom, free, k, r, match):
        return 'unsat', nodes[0]

    def dfs(dom, match):
        v = next((u for u in free if len(dom[u]) > 1), None)
        if v is None:
            return True
        for c in sorted(dom[v]):
            nodes[0] += 1
            if nodes[0] > limit:
                raise Budget
            d2 = [set(s) for s in dom]
            d2[v] = {c}
            m2 = dict(match)
            if propagate_separate(d2, free, k, r, m2) and dfs(d2, m2):
                return True
        return False

    try:
        return ('sat' if dfs(dom, match) else 'unsat'), nodes[0]
    except Budget:
        return 'limit', nodes[0]


def search_joint(pre, k, r):
    """DFS with joint domain consistency.  Returns (outcome, nodes, failures)."""
    pre = list(pre)
    r = list(r)
    nodes = 1
    sup = supports_fast(pre, k, r)
    if sup is None:
        return 'unsat', nodes, 0
    for v in [u for u, c in enumerate(pre) if c is None]:
        x = min(c for (u, c) in sup if u == v)
        pre[v] = x
        r[x] -= 1
        nodes += 1
        sup = supports_fast(pre, k, r)
        if sup is None:
            return 'fail', nodes, 1
    return 'sat', nodes, 0


# ------------------------------------------------------------- experiments

def exp_validate(rng, count=4000):
    bad = 0
    sep_bad = 0
    for _ in range(count):
        n = rng.randint(1, 10)
        k = rng.randint(1, 4)
        pre, r = generate(n, k, rng.choice([0, 0.2, 0.4]), rng.choice([0, 0.6]),
                          rng.randint(0, 2), rng)
        sb = supports_brute(pre, k, r)
        sf = supports_fast(pre, k, r)
        sn = supports_naive(pre, k, r)
        if not (sb == sf == sn):
            bad += 1
            print('MISMATCH', pre, r, sb, sf, sn)
        dom = separate_filter(pre, k, r)
        if sb is not None:
            if dom is None or any(c not in dom[v] for (v, c) in sb):
                sep_bad += 1
                print('SEPARATE NOT SOUND', pre, r)
    print(f'validate: {count} instances, joint mismatches {bad}, unsound separate {sep_bad}')
    return bad == 0 and sep_bad == 0


def exp_root(rng, reps=100):
    print('\nroot propagation (free vertex-color pairs removed; infeasible detection)')
    print('n,k,p,skew,delta,feasible,sep_detect,sep_removed_pct,joint_removed_pct')
    rows = []
    for n in (20, 50, 200):
        for k in (3, 5, 8):
            for skew in (0.0, 0.6):
                for delta in (0, 2):
                    p = 0.2
                    feas_n = det = 0
                    rs, rj = [], []
                    for _ in range(reps):
                        pre, r = generate(n, k, p, skew, delta, rng)
                        F = sum(1 for c in pre if c is None)
                        if F == 0:
                            continue
                        sj = supports_fast(pre, k, r)
                        dom = separate_filter(pre, k, r)
                        if sj is None:
                            if dom is None:
                                det += 1
                            continue
                        feas_n += 1
                        kept = sum(len(dom[v]) for v in range(n) if pre[v] is None)
                        rs.append(100.0 * (F * k - kept) / (F * k))
                        rj.append(100.0 * (F * k - len(sj)) / (F * k))
                    inf_n = reps - feas_n
                    row = (n, k, p, skew, delta, feas_n,
                           f'{det}/{inf_n}' if inf_n else '-',
                           f'{statistics.mean(rs):.1f}' if rs else '-',
                           f'{statistics.mean(rj):.1f}' if rj else '-')
                    rows.append(row)
                    print(','.join(map(str, row)))
                    sys.stdout.flush()
    return rows


def exp_infeasible(rng, target=100, max_attempts=1000000):
    print('\ninfeasible instances: detection by separate filtering at the root (beta=0.6, p=0.2)')
    print('n,k,delta,attempts,infeasible,sep_detect')
    for n in (20, 50, 100):
        for k in (3, 5, 8):
            for delta in (2, 8):
                attempts = found = det = 0
                while found < target and attempts < max_attempts:
                    attempts += 1
                    pre, r = generate(n, k, 0.2, 0.6, delta, rng)
                    if feasible(pre, k, r):
                        continue
                    found += 1
                    if separate_filter(pre, k, r) is None:
                        det += 1
                print(f'{n},{k},{delta},{attempts},{found},{det}')
                sys.stdout.flush()


def exp_search(rng, reps=50, limit=20000):
    print('\nsearch to first solution or refutation (node limit %d)' % limit)
    print('n,k,delta,instances,unsat,sep_limit,sep_nodes_median,sep_nodes_max,'
          'joint_nodes_median,joint_failures,sep_s,joint_s')
    for n in (20, 40, 60):
        for k in (3, 4):
            for delta in (1, 2):
                outs = []
                ts = tj = 0.0
                for _ in range(reps):
                    pre, r = generate(n, k, 0.2, 0.6, delta, rng)
                    t0 = time.perf_counter()
                    so, sn = search_separate(pre, k, r, limit)
                    t1 = time.perf_counter()
                    jo, jn, jf = search_joint(pre, k, r)
                    t2 = time.perf_counter()
                    ts += t1 - t0
                    tj += t2 - t1
                    if so != 'limit':
                        assert (so == 'sat') == (jo == 'sat'), (pre, r, so, jo)
                    outs.append((so, sn, jo, jn, jf))
                unsat = sum(1 for o in outs if o[2] == 'unsat')
                lim = sum(1 for o in outs if o[0] == 'limit')
                sn = [o[1] for o in outs]
                jn = [o[3] for o in outs]
                jf = sum(o[4] for o in outs)
                print(f'{n},{k},{delta},{reps},{unsat},{lim},{statistics.median(sn):.0f},'
                      f'{max(sn)},{statistics.median(jn):.0f},{jf},{ts:.1f},{tj:.1f}')
                sys.stdout.flush()


def exp_timing(rng):
    print('\nroot propagation time in seconds (feasible instances, p=0.2)')
    print('n,k,regions,joint_tests,joint_s,separate_s')
    for n in (1000, 10000, 100000):
        for k in (4, 16):
            pre, r = generate(n, k, 0.2, 0.0, 0, rng)
            st = {}
            t0 = time.perf_counter()
            sj = supports_fast(pre, k, r, st)
            t1 = time.perf_counter()
            if n <= 100000:
                dom = separate_filter(pre, k, r)
                t2 = time.perf_counter()
                sep = f'{t2 - t1:.2f}'
            else:
                sep = '-'
            print(f'{n},{k},{len(gaps_of(pre))},{st["tests"]},{t1 - t0:.2f},{sep}')
            sys.stdout.flush()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('what', choices=['validate', 'root', 'infeasible', 'search', 'timing', 'all'])
    ap.add_argument('--seed', type=int, default=2026)
    args = ap.parse_args()
    sys.setrecursionlimit(10000)
    experiments = [('validate', exp_validate), ('root', exp_root),
                   ('infeasible', exp_infeasible), ('search', exp_search),
                   ('timing', exp_timing)]
    for name, run in experiments:
        if args.what in (name, 'all'):
            run(random.Random(args.seed))


if __name__ == '__main__':
    main()
