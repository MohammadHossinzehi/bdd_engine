# bdd_engine

A Reduced Ordered Binary Decision Diagram (ROBDD) library written from scratch in pure Python, with zero dependencies.

A BDD is a canonical, compressed representation of a Boolean function. Because every function has exactly one node in the unique table, checking whether two formulas are equivalent is a single integer comparison. That one property powers hardware verification, model checking, product configuration and constraint solving.

## What is inside

| Feature | Notes |
|---|---|
| Unique table + `mk` | hash consing guarantees canonicity |
| ITE with computed cache | every connective (and, or, xor, implies, iff, not) is built on it |
| `restrict`, `exists`, `forall`, `compose` | cofactors, quantification, functional substitution |
| `rel_prod`, `rename`, `reachable` | symbolic image computation and fixpoint reachability for model checking |
| `satcount`, `anysat`, `allsat`, `models` | exact model counting that correctly accounts for skipped levels |
| Formula parser | `! ~ & ^ | -> <->` with correct precedence, right associative implication |
| Variable ordering | `transfer` rebuilds under any order, `sift` searches for a smaller one |
| `to_dot` | Graphviz output |
| `n_queens` demo | encodes the puzzle as one Boolean function and counts all solutions |

## Run it

Requires Python 3.9 or newer.

```bash
python robdd.py eval "(a & b) | !c"
python robdd.py equiv "a -> b" "!b -> !a"      # EQUIVALENT
python robdd.py queens 8                        # 92 solutions
python -m unittest discover -s tests
```

Library use:

```python
from robdd import BDD

b = BDD()
f = b.parse("(x & y) | z")
print(b.satcount(f, 3))              # 5
print(b.exists(["x"], f))            # node id of (y | z)
print(b.anysat(f))                   # one satisfying assignment
```

Symbolic reachability of a 3 bit counter lives in `tests/test_robdd.py`: it builds the transition relation as a BDD, then iterates `image(R) union R` until the fixpoint without ever enumerating states.

## Design decisions

* Nodes are plain integers indexing parallel lists (`_var`, `_lo`, `_hi`). Terminals are 0 and 1, so equality of functions is `==` on ints and there are no object allocations on the hot path.
* One recursive primitive, `ite`, with a memo table. Everything else is a thin wrapper, which keeps the correctness argument small.
* `satcount` multiplies by `2^(gap)` for every level skipped between a node and its children, which is the classic place for off by one bugs. Tests cross check it against explicit enumeration, including a function that skips several levels.
* Variable order dominates BDD size. The ordering test builds `x0&y0 | x1&y1 | ...` under an interleaved order (10 nodes) and a separated order (dozens of nodes), proves they represent the same function, then checks that `sift` recovers a near optimal order. Sifting here is implemented by rebuilding, which is simple and obviously correct rather than the in place swap of the original paper.

## Testing

The suite (16 tests) includes randomized formulas checked against a Python truth table evaluator, De Morgan and tautology identities, quantifier and composition laws, parser error handling, the n queens counts 2, 10, 4 for n = 4, 5, 6, and two reachability problems including one with provably unreachable states.
