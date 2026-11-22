#!/usr/bin/env python3
"""Randomized differential test: synthesis.Engine and synthesis.ResumeEngine
against the harness decoder run whole (certified_decode, unmodified), after
every edit of long random chained edit sequences: overlays at read keys,
withdrawals, rows inserted at keys a cone saw missing and at keys no cone
reads, equal-value rewrites, and fresh random rows. Harness tables at many
seeds, not only 11 and 23. usage: fuzz_s2.py <harness/run.py> [seeds] [steps]"""
import os, random, sys
from fractions import Fraction
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import synthesis as SY


def fuzz(h, seed, steps):
    rng = random.Random(1000 + seed)
    table = h.build_table(seed)
    queries = h.queries_for(table, seed)
    engs = [SY.Engine(h, table, queries), SY.ResumeEngine(h, table, queries)]
    for e in engs:
        e.build()
    toks = sorted({t for row in table.values() for t, _w in row}) or [0]
    keys = engs[0].keys
    for step in range(steps):
        read = sorted({k for q in keys for k in engs[0].state[q][1]}, key=repr)
        pool = read if rng.random() < 0.8 else sorted(table, key=repr)
        rk = rng.choice(pool)
        if rng.random() < 0.1:  # a key one token past a read key: may or may not be read
            rk = tuple(rk) + (rng.choice(toks),)
        row = dict.get(engs[0].table, rk)
        r = rng.random()
        if row is not None and r < 0.4:
            tok, _w = rng.choice(row)
            new = SY.overlay(row, tok, rng.choice((Fraction(2), Fraction(1, 2), Fraction(3), Fraction(1, 3))))
        elif row is not None and r < 0.55:
            new = None
        elif row is not None and r < 0.65:
            new = list(row)  # equal value: early cutoff
        else:
            k = rng.randint(1, min(3, len(toks)))
            new = [(t, Fraction(rng.randint(1, 10), 10)) for t in rng.sample(toks, k)]
        for e in engs:
            e.edit(rk, new)
        ref, _ = SY.scratch(h, engs[0].table, keys)
        for e, name in zip(engs, ("whole-query", "resume")):
            if dict(e.table) != dict(engs[0].table):
                return "seed %d step %d: %s engine table drifted" % (seed, step, name)
            bad = [k for k in keys if e.verdict(k) != ref[k]]
            if bad:
                return "seed %d step %d: %s engine disagrees on %d of %d queries (edit at %r)" % (
                    seed, step, name, len(bad), len(keys), rk)
    return None


def main():
    h = SY.load_harness(sys.argv[1])
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 80
    bad = []
    for s in range(seeds):
        r = fuzz(h, s, steps)
        if r:
            bad.append(r)
    print("synthesis: %d harness seeds x %d chained edits, both engines vs the whole decoder after every edit" % (seeds, steps))
    for b in bad[:10]:
        print("DISAGREE", b)
    print("FUZZ s2: %s (%d disagreements)" % ("PASS" if not bad else "FAIL", len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
