"""Reduced Ordered Binary Decision Diagrams (ROBDD) from scratch.

Nodes live in a unique table so every Boolean function has exactly one
node (canonicity): equivalence checking is pointer equality.
Terminals are 0 (False) and 1 (True). Internal node ids start at 2.
"""
from __future__ import annotations
import re
import sys

sys.setrecursionlimit(100000)


class BDD:
    def __init__(self, var_names=()):
        self.names = []          # level -> name
        self.level = {}          # name -> level
        self._var = [None, None]  # node -> level (terminals get inf)
        self._lo = [0, 1]
        self._hi = [0, 1]
        self._unique = {}
        self._ite_cache = {}
        self._quant_cache = {}
        for n in var_names:
            self.declare(n)

    # ---- variables / nodes -------------------------------------------
    def declare(self, name):
        if name not in self.level:
            self.level[name] = len(self.names)
            self.names.append(name)
        return self.var(name)

    def _lvl(self, u):
        return len(self.names) + 1 if u < 2 else self._var[u]

    def mk(self, lvl, lo, hi):
        if lo == hi:
            return lo
        key = (lvl, lo, hi)
        u = self._unique.get(key)
        if u is None:
            u = len(self._var)
            self._var.append(lvl)
            self._lo.append(lo)
            self._hi.append(hi)
            self._unique[key] = u
        return u

    def var(self, name):
        if name not in self.level:
            self.declare(name)
        return self.mk(self.level[name], 0, 1)

    true = 1
    false = 0

    # ---- core: ITE ---------------------------------------------------
    def ite(self, f, g, h):
        if f == 1:
            return g
        if f == 0:
            return h
        if g == h:
            return g
        if g == 1 and h == 0:
            return f
        key = (f, g, h)
        r = self._ite_cache.get(key)
        if r is not None:
            return r
        top = min(self._lvl(f), self._lvl(g), self._lvl(h))
        f0, f1 = self._cof(f, top)
        g0, g1 = self._cof(g, top)
        h0, h1 = self._cof(h, top)
        r = self.mk(top, self.ite(f0, g0, h0), self.ite(f1, g1, h1))
        self._ite_cache[key] = r
        return r

    def _cof(self, u, lvl):
        if u >= 2 and self._var[u] == lvl:
            return self._lo[u], self._hi[u]
        return u, u

    # ---- connectives ---------------------------------------------------
    def neg(self, u): return self.ite(u, 0, 1)
    def and_(self, a, b): return self.ite(a, b, 0)
    def or_(self, a, b): return self.ite(a, 1, b)
    def xor(self, a, b): return self.ite(a, self.neg(b), b)
    def implies(self, a, b): return self.ite(a, b, 1)
    def iff(self, a, b): return self.ite(a, b, self.neg(b))

    def conj(self, xs):
        r = 1
        for x in xs:
            r = self.and_(r, x)
        return r

    def disj(self, xs):
        r = 0
        for x in xs:
            r = self.or_(r, x)
        return r

    # ---- restriction, quantification, composition ----------------------
    def restrict(self, u, assignment):
        """Cofactor u by {name: bool}."""
        amap = {self.level[n]: bool(v) for n, v in assignment.items()}
        memo = {}

        def go(x):
            if x < 2:
                return x
            if x in memo:
                return memo[x]
            lv = self._var[x]
            if lv in amap:
                r = go(self._hi[x] if amap[lv] else self._lo[x])
            else:
                r = self.mk(lv, go(self._lo[x]), go(self._hi[x]))
            memo[x] = r
            return r
        return go(u)

    def exists(self, names, u):
        return self._quantify(names, u, self.or_)

    def forall(self, names, u):
        return self._quantify(names, u, self.and_)

    def _quantify(self, names, u, op):
        lvls = frozenset(self.level[n] for n in names)
        memo = {}

        def go(x):
            if x < 2:
                return x
            if x in memo:
                return memo[x]
            lo, hi = go(self._lo[x]), go(self._hi[x])
            lv = self._var[x]
            r = op(lo, hi) if lv in lvls else self.mk(lv, lo, hi)
            memo[x] = r
            return r
        return go(u)

    def compose(self, u, name, g):
        """Substitute function g for variable `name` in u."""
        v = self.level[name]
        memo = {}

        def go(x):
            if x < 2 or self._var[x] > v:
                return x
            if x in memo:
                return memo[x]
            if self._var[x] == v:
                r = self.ite(g, self._hi[x], self._lo[x])
            else:
                r = self.ite(self.mk(self._var[x], 0, 1), go(self._hi[x]), go(self._lo[x]))
            memo[x] = r
            return r
        return go(u)

    def rel_prod(self, names, a, b):
        """exists names . (a AND b), used for symbolic image computation."""
        return self.exists(names, self.and_(a, b))

    def rename(self, u, mapping):
        """Rename variables via sequential composition (mapping name->name)."""
        for old, new in mapping.items():
            u = self.compose(u, old, self.var(new))
        return u

    # ---- queries -------------------------------------------------------
    def evaluate(self, u, assignment):
        while u >= 2:
            u = self._hi[u] if assignment[self.names[self._var[u]]] else self._lo[u]
        return u == 1

    def support(self, u):
        seen, out = set(), set()
        stack = [u]
        while stack:
            x = stack.pop()
            if x < 2 or x in seen:
                continue
            seen.add(x)
            out.add(self.names[self._var[x]])
            stack += [self._lo[x], self._hi[x]]
        return sorted(out, key=self.level.get)

    def size(self, *roots):
        seen = set()
        stack = list(roots)
        while stack:
            x = stack.pop()
            if x < 2 or x in seen:
                continue
            seen.add(x)
            stack += [self._lo[x], self._hi[x]]
        return len(seen)

    def satcount(self, u, nvars=None):
        n = len(self.names) if nvars is None else nvars
        memo = {}

        def go(x):  # models over variables at levels >= level(x)
            if x == 0:
                return 0
            if x == 1:
                return 1
            if x in memo:
                return memo[x]
            lv = self._var[x]
            lo, hi = self._lo[x], self._hi[x]
            r = go(lo) * (1 << (self._lvl2(lo, n) - lv - 1)) + \
                go(hi) * (1 << (self._lvl2(hi, n) - lv - 1))
            memo[x] = r
            return r
        if u < 2:
            return u * (1 << n)
        return go(u) * (1 << self._var[u])

    def _lvl2(self, u, n):
        return n if u < 2 else self._var[u]

    def anysat(self, u):
        if u == 0:
            return None
        out = {}
        while u >= 2:
            nm = self.names[self._var[u]]
            if self._hi[u] != 0:
                out[nm] = True
                u = self._hi[u]
            else:
                out[nm] = False
                u = self._lo[u]
        return out

    def allsat(self, u):
        """Yield partial assignments (cubes) covering all models."""
        def go(x, cube):
            if x == 0:
                return
            if x == 1:
                yield dict(cube)
                return
            nm = self.names[self._var[x]]
            cube[nm] = False
            yield from go(self._lo[x], cube)
            cube[nm] = True
            yield from go(self._hi[x], cube)
            del cube[nm]
        yield from go(u, {})

    def models(self, u, names=None):
        """Enumerate full assignments over `names` (default all variables)."""
        names = list(names or self.names)
        for cube in self.allsat(u):
            free = [n for n in names if n not in cube]
            for bits in range(1 << len(free)):
                m = dict(cube)
                for i, n in enumerate(free):
                    m[n] = bool(bits >> i & 1)
                yield {n: m[n] for n in names}

    # ---- parsing ---------------------------------------------------------
    _TOK = re.compile(r"\s*(<->|->|[()!&|^~]|[A-Za-z_][A-Za-z0-9_]*|[01])")

    def parse(self, text):
        toks, pos = [], 0
        text = text.strip()
        while pos < len(text):
            m = self._TOK.match(text, pos)
            if not m:
                raise ValueError(f"bad character at {pos}: {text[pos:pos+8]!r}")
            toks.append(m.group(1))
            pos = m.end()
        i = [0]

        def peek(): return toks[i[0]] if i[0] < len(toks) else None

        def eat(t=None):
            x = peek()
            if x is None or (t and x != t):
                raise ValueError(f"expected {t!r}, got {x!r}")
            i[0] += 1
            return x

        def p_iff():
            a = p_imp()
            while peek() == "<->":
                eat(); a = self.iff(a, p_imp())
            return a

        def p_imp():  # right associative
            a = p_or()
            if peek() == "->":
                eat(); return self.implies(a, p_imp())
            return a

        def p_or():
            a = p_xor()
            while peek() == "|":
                eat(); a = self.or_(a, p_xor())
            return a

        def p_xor():
            a = p_and()
            while peek() == "^":
                eat(); a = self.xor(a, p_and())
            return a

        def p_and():
            a = p_not()
            while peek() == "&":
                eat(); a = self.and_(a, p_not())
            return a

        def p_not():
            if peek() in ("!", "~"):
                eat(); return self.neg(p_not())
            return p_atom()

        def p_atom():
            t = eat()
            if t == "(":
                a = p_iff(); eat(")"); return a
            if t == "0": return 0
            if t == "1": return 1
            if t in ("<->", "->", ")", "&", "|", "^"):
                raise ValueError(f"unexpected {t!r}")
            return self.var(t)

        r = p_iff()
        if peek() is not None:
            raise ValueError(f"trailing input at token {peek()!r}")
        return r

    # ---- ordering ----------------------------------------------------------
    def transfer(self, roots, order):
        """Rebuild roots in a fresh manager using variable `order`."""
        new = BDD(order)
        memo = {}

        def go(x):
            if x < 2:
                return x
            if x in memo:
                return memo[x]
            v = new.var(self.names[self._var[x]])
            r = new.ite(v, go(self._hi[x]), go(self._lo[x]))
            memo[x] = r
            return r
        return new, [go(r) for r in roots]

    def sift(self, roots, passes=2):
        """Rudell-style sifting (by rebuild): move each variable to its best
        position. Returns (new_manager, new_roots, order)."""
        order = list(self.names)
        mgr, rts = self, list(roots)
        best = mgr.size(*rts)
        for _ in range(passes):
            improved = False
            for v in list(order):
                base = [x for x in order if x != v]
                cand_best, cand_order = best, order
                for pos in range(len(order)):
                    cand = base[:pos] + [v] + base[pos:]
                    if cand == order:
                        continue
                    m, r = self.transfer(roots, cand) if mgr is self else mgr.transfer(rts, cand)
                    s = m.size(*r)
                    if s < cand_best:
                        cand_best, cand_order = s, cand
                if cand_order != order:
                    mgr, rts = (self.transfer(roots, cand_order) if mgr is self
                                else mgr.transfer(rts, cand_order))
                    order, best, improved = cand_order, cand_best, True
            if not improved:
                break
        return mgr, rts, order

    # ---- output --------------------------------------------------------------
    def to_dot(self, roots, labels=None):
        roots = roots if isinstance(roots, (list, tuple)) else [roots]
        lines = ["digraph BDD {", '  node [shape=circle];',
                 '  0 [shape=box,label="0"];', '  1 [shape=box,label="1"];']
        seen, stack = set(), list(roots)
        for i, r in enumerate(roots):
            lab = labels[i] if labels else f"f{i}"
            lines.append(f'  r{i} [shape=plaintext,label="{lab}"]; r{i} -> {r};')
        while stack:
            x = stack.pop()
            if x < 2 or x in seen:
                continue
            seen.add(x)
            lines.append(f'  {x} [label="{self.names[self._var[x]]}"];')
            lines.append(f"  {x} -> {self._lo[x]} [style=dashed];")
            lines.append(f"  {x} -> {self._hi[x]};")
            stack += [self._lo[x], self._hi[x]]
        lines.append("}")
        return "\n".join(lines)


# ---------------------------------------------------------------------------
# Applications
# ---------------------------------------------------------------------------

def n_queens(n):
    """Return (bdd, root) of the n-queens constraint over n*n variables."""
    b = BDD([f"q{r}_{c}" for r in range(n) for c in range(n)])
    q = lambda r, c: b.var(f"q{r}_{c}")
    f = 1
    for r in range(n):
        f = b.and_(f, b.disj(q(r, c) for c in range(n)))  # a queen per row
    for r1 in range(n):
        for c1 in range(n):
            for r2 in range(r1, n):
                for c2 in range(n):
                    if (r2, c2) <= (r1, c1):
                        continue
                    if c1 == c2 or r1 == r2 or abs(r1 - r2) == abs(c1 - c2):
                        f = b.and_(f, b.or_(b.neg(q(r1, c1)), b.neg(q(r2, c2))))
    return b, f


def reachable(b, init, trans, cur, nxt):
    """Symbolic BFS: least fixpoint of image(R) union init.
    `cur`/`nxt` are lists of variable names (pairwise corresponding)."""
    ren = dict(zip(nxt, cur))
    reach = init
    while True:
        img = b.rename(b.rel_prod(cur, reach, trans), ren)
        new = b.or_(reach, img)
        if new == reach:
            return reach
        reach = new


def _cli(argv):
    import argparse
    ap = argparse.ArgumentParser(description="ROBDD toolkit")
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("eval", help="analyse a Boolean formula")
    p.add_argument("formula")
    p.add_argument("--dot", action="store_true")
    p = sub.add_parser("equiv", help="check equivalence of two formulas")
    p.add_argument("a"); p.add_argument("b")
    p = sub.add_parser("queens", help="count n-queens solutions")
    p.add_argument("n", type=int)
    a = ap.parse_args(argv)
    if a.cmd == "eval":
        b = BDD(); u = b.parse(a.formula)
        print("variables :", b.support(u))
        print("nodes     :", b.size(u))
        print("models    :", b.satcount(u, len(b.names)))
        print("example   :", b.anysat(u))
        print("tautology :", u == 1, " unsat:", u == 0)
        if a.dot:
            print(b.to_dot(u, [a.formula]))
    elif a.cmd == "equiv":
        b = BDD(); x, y = b.parse(a.a), b.parse(a.b)
        if x == y:
            print("EQUIVALENT")
        else:
            print("DIFFERENT, counterexample:", b.anysat(b.xor(x, y)))
    else:
        b, f = n_queens(a.n)
        print(f"{a.n}-queens: {b.satcount(f)} solutions, BDD nodes: {b.size(f)}")
    return 0


if __name__ == "__main__":
    sys.exit(_cli(sys.argv[1:]))
