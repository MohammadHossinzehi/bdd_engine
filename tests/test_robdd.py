import itertools, os, random, sys, unittest
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
from robdd import BDD, n_queens, reachable


def truth(b, u, names):
    return [b.evaluate(u, dict(zip(names, bits)))
            for bits in itertools.product([False, True], repeat=len(names))]


class TestBasics(unittest.TestCase):
    def test_canonicity_de_morgan(self):
        b = BDD("abc")
        self.assertEqual(b.parse("!(a & b)"), b.parse("!a | !b"))
        self.assertEqual(b.parse("a -> b"), b.parse("!a | b"))
        self.assertEqual(b.parse("a ^ b"), b.parse("(a | b) & !(a & b)"))

    def test_tautology_and_contradiction(self):
        b = BDD()
        self.assertEqual(b.parse("a | !a"), 1)
        self.assertEqual(b.parse("a & !a"), 0)
        self.assertEqual(b.parse("(a -> b) & (b -> c) -> (a -> c)"), 1)

    def test_parser_precedence_and_errors(self):
        b = BDD()
        self.assertEqual(b.parse("a | b & c"), b.parse("a | (b & c)"))
        self.assertEqual(b.parse("a -> b -> c"), b.parse("a -> (b -> c)"))
        for bad in ["a &", "(a", "a b", "& a", "a $ b"]:
            with self.assertRaises(ValueError):
                b.parse(bad)

    def test_random_formulas_against_truth_table(self):
        rnd = random.Random(1)
        names = list("abcde")
        fns = {"&": lambda x, y: x and y, "|": lambda x, y: x or y,
               "^": lambda x, y: x != y, "->": lambda x, y: (not x) or y,
               "<->": lambda x, y: x == y}

        def gen(d):
            if d == 0 or rnd.random() < .2:
                n = rnd.choice(names)
                if rnd.random() < .3:
                    return "!" + n, lambda e, n=n: not e[n]
                return n, lambda e, n=n: e[n]
            op = rnd.choice(list(fns))
            (s1, f1), (s2, f2) = gen(d - 1), gen(d - 1)
            return f"({s1} {op} {s2})", lambda e: fns[op](f1(e), f2(e))

        for _ in range(60):
            b = BDD(names)
            s, fn = gen(4)
            u = b.parse(s)
            for bits in itertools.product([False, True], repeat=5):
                env = dict(zip(names, bits))
                self.assertEqual(b.evaluate(u, env), fn(env), s)


class TestOps(unittest.TestCase):
    def test_satcount_matches_enumeration(self):
        b = BDD("abcd")
        u = b.parse("(a & b) | (c ^ d)")
        self.assertEqual(b.satcount(u), sum(truth(b, u, "abcd")))
        self.assertEqual(sum(1 for _ in b.models(u)), b.satcount(u))
        self.assertEqual(b.satcount(1), 16)
        self.assertEqual(b.satcount(0), 0)

    def test_satcount_with_skipped_levels(self):
        b = BDD("abcde")
        u = b.parse("a & e")
        self.assertEqual(b.satcount(u), 8)

    def test_restrict_exists_forall(self):
        b = BDD("abc")
        u = b.parse("(a & b) | c")
        self.assertEqual(b.restrict(u, {"c": True}), 1)
        self.assertEqual(b.restrict(u, {"c": False}), b.parse("a & b"))
        self.assertEqual(b.exists(["a"], u), b.parse("b | c"))
        self.assertEqual(b.forall(["a"], u), b.var("c"))
        self.assertEqual(b.forall(["a", "b"], u), b.var("c"))

    def test_compose(self):
        b = BDD("abc")
        u = b.parse("a & b")
        self.assertEqual(b.compose(u, "a", b.parse("b | c")), b.parse("(b | c) & b"))
        self.assertEqual(b.compose(u, "a", b.parse("c")), b.parse("c & b"))

    def test_anysat_and_allsat(self):
        b = BDD("abc")
        u = b.parse("(a | b) & !c")
        self.assertTrue(b.evaluate(u, {**{n: False for n in "abc"}, **b.anysat(u)}))
        self.assertIsNone(b.anysat(0))
        cubes = list(b.allsat(u))
        self.assertTrue(all(b.restrict(u, c) == 1 for c in cubes))

    def test_support(self):
        b = BDD("abcd")
        self.assertEqual(b.support(b.parse("(a & d) | (a & !d)")), ["a"])

    def test_dot(self):
        b = BDD(); u = b.parse("a & b")
        self.assertIn("digraph", b.to_dot(u))


class TestOrdering(unittest.TestCase):
    def pairs(self, order):
        b = BDD(order)
        return b, b.disj(b.and_(b.var(f"x{i}"), b.var(f"y{i}")) for i in range(5))

    def test_order_changes_size_not_function(self):
        good = [v for i in range(5) for v in (f"x{i}", f"y{i}")]
        bad = [f"x{i}" for i in range(5)] + [f"y{i}" for i in range(5)]
        bg, fg = self.pairs(good)
        bb, fb = self.pairs(bad)
        self.assertEqual(bg.size(fg), 10)
        self.assertGreater(bb.size(fb), 30)
        self.assertEqual(bg.satcount(fg), bb.satcount(fb))

    def test_sift_recovers_good_order(self):
        bad = [f"x{i}" for i in range(5)] + [f"y{i}" for i in range(5)]
        b, f = self.pairs(bad)
        m, (g,), order = b.sift([f])
        self.assertLessEqual(m.size(g), 12)
        self.assertEqual(m.satcount(g), b.satcount(f))


class TestApplications(unittest.TestCase):
    def test_queens_counts(self):
        known = {4: 2, 5: 10, 6: 4}
        for n, c in known.items():
            b, f = n_queens(n)
            self.assertEqual(b.satcount(f), c)
        b, f = n_queens(6)
        for m in b.models(f):
            pass  # enumerates without error

    def test_counter_reachability(self):
        # 3-bit counter that increments each step from 0 -> reaches all 8.
        b = BDD(["c0", "c1", "c2", "n0", "n1", "n2"])
        c = [b.var(f"c{i}") for i in range(3)]
        n = [b.var(f"n{i}") for i in range(3)]
        carry = 1
        trans = 1
        for i in range(3):
            trans = b.and_(trans, b.iff(n[i], b.xor(c[i], carry)))
            carry = b.and_(carry, c[i])
        init = b.conj(b.neg(x) for x in c)
        r = reachable(b, init, trans, ["c0", "c1", "c2"], ["n0", "n1", "n2"])
        self.assertEqual(b.satcount(r, 6) // 8, 8)

    def test_saturating_counter_unreachable_states(self):
        # 2-bit value that only moves 0->1->2->1->0, never reaches 3.
        b = BDD(["a", "b", "na", "nb"])
        s = lambda x, y: b.and_(b.var("a") if x else b.neg(b.var("a")),
                                 b.var("b") if y else b.neg(b.var("b")))
        t = lambda x, y: b.and_(b.var("na") if x else b.neg(b.var("na")),
                                 b.var("nb") if y else b.neg(b.var("nb")))
        edges = [((0, 0), (0, 1)), ((0, 1), (1, 0)), ((1, 0), (0, 1)), ((0, 1), (0, 0))]
        trans = b.disj(b.and_(s(*u), t(*v)) for u, v in edges)
        r = reachable(b, s(0, 0), trans, ["a", "b"], ["na", "nb"])
        self.assertEqual(r, b.disj([s(0, 0), s(0, 1), s(1, 0)]))
        self.assertEqual(b.and_(r, s(1, 1)), 0)


if __name__ == "__main__":
    unittest.main()
