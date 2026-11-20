#!/usr/bin/env python3
"""The empirical program for the parametric rewritable
language model, at fixture scale.

The fixture is a synthetic archived-row table in the shape
of the deterministic decoding line: rows keyed by prefix,
each row a list of (token, weight) pairs, a completeness
rule (length three from the root), a checkpoint name and a
protocol name. It is generated on this machine from a fixed
seed and labeled synthetic everywhere it is reported. The
real checkpoint fixtures of the deterministic decoding line
are not on this machine; every cell that needs them is
printed unmeasured in the results, with the blocker named.

Engines, all reading the same table:
  certified  the certified best first decoder of the
             specification: a max heap of prefixes by score;
             a missing row leaves the prefix as an unresolved
             branch whose score is an upper bound; the best
             complete answer is certified only when it beats
             or ties the heap maximum and every unresolved
             bound.
  greedy     at each step take the heaviest next token.
  sampled    at each step sample proportional to
             weight ** (1 / temperature), seeded.

Costs are counted in row lookups and heap pops, the two
operations the engines perform; no wall clock is claimed.

No benchmark gaming: one contract per battery, stated in
the results; the held out pass reruns the serving battery on
a second fixture seed the engines were not tuned against
(there is nothing to tune: the engines have no free
constants beyond the stated temperatures and the bound).
"""

import heapq
import itertools
import random
from fractions import Fraction

VOCAB = 24
DEPTH = 3
QUERIES_PER_SEED = 24
RUNS = 20


def build_table(seed):
    rng = random.Random(seed)
    table = {}

    def row_for(prefix):
        k = rng.randint(3, 6)
        toks = rng.sample(range(VOCAB), k)
        raw = [(t, rng.randint(1, 9)) for t in sorted(toks)]
        total = sum(w for _, w in raw)
        # Rows are probability rows, as the specification
        # requires: each entry is its weight over the row
        # sum. A path score is then a product of fractions
        # at most one, so a prefix's score bounds every
        # completion beneath it — the premise the
        # certification rule stands on.
        return [(t, Fraction(w, total)) for t, w in raw]

    frontier = [[]]
    for depth in range(DEPTH):
        nxt = []
        for pre in frontier:
            # The root row always exists: a checkpoint with no
            # root row is degenerate, not a test case. Deeper
            # rows are present with probability 0.9.
            if depth == 0 or rng.random() < 0.9:
                row = row_for(pre)
                table[tuple(pre)] = row
                nxt.extend(pre + [t] for t, _ in row)
        frontier = nxt
    return table


def done(seq):
    return len(seq) == DEPTH


def row_of(table, pre):
    return table.get(tuple(pre))


def path_score(table, pre, seq):
    """Product of the recorded weights along seq from pre."""
    score = Fraction(1)
    cur = list(pre)
    for x in seq:
        row = row_of(table, cur)
        if row is None:
            return None
        w = dict(row).get(x)
        if w is None:
            return None
        score *= w
        cur = cur + [x]
    return score


def completes_within(table, pre, bound):
    """Exhaustive oracle: every complete sequence reachable
    from pre within bound further tokens, with its score, and
    every frontier bound (the score of a prefix that cannot
    be expanded: missing row, or the depth bound reached)."""
    out = []
    bounds = []

    def walk(cur, rest, score):
        if done(cur):
            out.append((list(cur[len(pre):]), score))
            return
        if rest <= 0:
            bounds.append(score)
            return
        row = row_of(table, cur)
        if row is None:
            bounds.append(score)
            return
        for tok, w in row:
            walk(cur + [tok], rest - 1, score * w)

    walk(list(pre), bound, Fraction(1))
    return out, bounds


def certified_decode(table, pre, bound=DEPTH):
    """The certified best first decoder. Returns a dict with
    the answer (or None), whether it is certified, its score,
    the blocking bound where certification fails, and the
    counted cost."""
    cost = {"lookups": 0, "pops": 0}
    counter = itertools.count()
    heap = [(Fraction(-1), next(counter), list(pre), Fraction(1))]
    unresolved = []
    best = None
    best_score = None
    while heap:
        negscore, _, cur, score = heapq.heappop(heap)
        cost["pops"] += 1
        score = -negscore
        if best_score is not None and score < best_score:
            break
        if done(cur):
            if best_score is None or score > best_score:
                best, best_score = list(cur[len(pre):]), score
            continue
        if len(cur) - len(pre) >= bound:
            unresolved.append(score)
            continue
        cost["lookups"] += 1
        row = row_of(table, cur)
        if row is None:
            unresolved.append(score)
            continue
        for tok, w in row:
            heapq.heappush(heap, (-(score * w), next(counter),
                                  cur + [tok], score * w))
    blocking = None
    if best is not None:
        limits = unresolved + ([-heap[0][0]] if heap else [])
        over = [b for b in limits if b > best_score]
        if over:
            blocking = min(over)
    certified = best is not None and blocking is None
    return {"answer": best, "certified": certified,
            "score": best_score, "blocking": blocking,
            "cost": cost}


def greedy_decode(table, pre, bound=DEPTH):
    cost = {"lookups": 0}
    cur = list(pre)
    while not done(cur) and len(cur) - len(pre) < bound:
        cost["lookups"] += 1
        row = row_of(table, cur)
        if row is None:
            return {"answer": None, "cost": cost}
        tok, _ = max(row, key=lambda e: e[1])
        cur = cur + [tok]
    if done(cur):
        return {"answer": cur[len(pre):], "cost": cost}
    return {"answer": None, "cost": cost}


def sampled_decode(table, pre, temperature, rng, bound=DEPTH):
    cost = {"lookups": 0}
    cur = list(pre)
    while not done(cur) and len(cur) - len(pre) < bound:
        cost["lookups"] += 1
        row = row_of(table, cur)
        if row is None:
            return {"answer": None, "cost": cost}
        weights = [float(w) ** (1.0 / temperature) for _, w in row]
        total = sum(weights)
        r = rng.random() * total
        acc = 0.0
        pick = row[-1][0]
        for (tok, _), w in zip(row, weights):
            acc += w
            if r <= acc:
                pick = tok
                break
        cur = cur + [pick]
    if done(cur):
        return {"answer": cur[len(pre):], "cost": cost}
    return {"answer": None, "cost": cost}


def queries_for(table, seed):
    """Queries at every depth: the root, length one prefixes
    reached from the root row, and length two prefixes reached
    from length one rows — whether or not the prefix carries
    its own row (a missing row is the unresolved case, still a
    lawful query)."""
    rng = random.Random(seed + 777)
    ones = [[t] for t, _ in table.get((), [])]
    twos = []
    for p in ones:
        for t, _ in table.get(tuple(p), []):
            twos.append(p + [t])
    rng.shuffle(ones)
    rng.shuffle(twos)
    third = QUERIES_PER_SEED // 3
    return ([[] for _ in range(third)] + ones[:third]
            + twos[: QUERIES_PER_SEED - 2 * third])


def serving_battery(seed):
    table = build_table(seed)
    queries = queries_for(table, seed)
    rows = []
    for qi, pre in enumerate(queries):
        oracle, bounds = completes_within(table, pre, DEPTH - len(pre))
        best_score = max((s for _, s in oracle), default=None)
        uniq_best = sum(1 for _, s in oracle if s == best_score) == 1
        cert = certified_decode(table, pre, DEPTH - len(pre))
        greedy = greedy_decode(table, pre, DEPTH - len(pre))
        greedy_score = (path_score(table, pre, greedy["answer"])
                        if greedy["answer"] else None)
        samp = {}
        for temp in (1.0, 0.7):
            rng = random.Random(seed * 1000 + qi * 17 + int(temp * 10))
            outs = []
            costs = []
            for _ in range(RUNS):
                r = sampled_decode(table, pre, temp, rng,
                                   DEPTH - len(pre))
                outs.append(tuple(r["answer"]) if r["answer"] else None)
                costs.append(r["cost"]["lookups"])
            distinct = len(set(outs))
            scores = [path_score(table, pre, list(o)) if o else None
                      for o in outs]
            ratios = [s / best_score for s in scores
                      if s is not None and best_score]
            samp[temp] = {
                "distinct": distinct,
                "mean_cost": sum(costs) / len(costs),
                "worst_ratio": min(ratios) if ratios else None,
                "best_hits": sum(1 for o, s in zip(outs, scores)
                                 if s == best_score),
                "none_rate": sum(1 for o in outs if o is None) / len(outs),
            }
        rows.append({
            "pre": pre, "oracle_count": len(oracle),
            "best_score": best_score, "uniq_best": uniq_best,
            "cert": cert, "greedy_score": greedy_score,
            "greedy_cost": greedy["cost"]["lookups"],
            "samp": samp,
        })
    return rows


def summarize(rows, label):
    n = len(rows)
    cert_rate = sum(1 for r in rows if r["cert"]["certified"]) / n
    agree = [r for r in rows if r["cert"]["certified"]]
    score_ok = all(r["cert"]["score"] == r["best_score"] for r in agree)
    cert_cost = (sum(r["cert"]["cost"]["lookups"] + r["cert"]["cost"]["pops"]
                     for r in agree) / len(agree)) if agree else None
    greedy_ratio = [r["greedy_score"] / r["best_score"] for r in rows
                    if r["greedy_score"] and r["best_score"]]
    lines = [f"### Serving battery ({label})",
             f"queries: {n}",
             f"certified rate: {cert_rate:.3f}",
             f"certified score equals the exhaustive oracle maximum "
             f"on every certified query: {score_ok}",
             f"mean certified cost (lookups + pops) per certified "
             f"answer: {cert_cost}",
             f"greedy mean lookups: "
             f"{sum(r['greedy_cost'] for r in rows) / n:.2f}",
             f"greedy score ratio to the best, mean "
             f"{sum(greedy_ratio) / len(greedy_ratio):.3f}, worst "
             f"{min(greedy_ratio):.3f}" if greedy_ratio else
             "greedy score ratio to the best: no scored queries"]
    for temp in (1.0, 0.7):
        d = [r["samp"][temp]["distinct"] for r in rows]
        wr = [r["samp"][temp]["worst_ratio"] for r in rows
              if r["samp"][temp]["worst_ratio"] is not None]
        bh = sum(r["samp"][temp]["best_hits"] for r in rows)
        lines.append(
            f"sampled T={temp}: distinct outputs per query over "
            f"{RUNS} repeats, mean {sum(d) / len(d):.2f}, max "
            f"{max(d)}; runs landing on the best completion: "
            f"{bh} of {n * RUNS}; worst score ratio to the best: "
            f"{min(wr):.3f}")
    blocked = [r for r in rows if not r["cert"]["certified"]
               and r["cert"]["blocking"] is not None]
    lines.append(f"queries blocked by an unresolved bound: "
                 f"{len(blocked)} of {n}")
    return lines


def overlay_battery(seed):
    """Edit locality. The integer table is read as fractions
    (weight over ten); fifty single key overlays are applied
    one at a time. For every complete path of every query:
    a path that touches the edited key changes score by
    exactly the multiplier; a path that does not keeps its
    fraction exactly. Both directions are checked, not
    sampled."""
    table = build_table(seed)
    queries = queries_for(table, seed)

    def fscore(pre, seq, mult_key=None, mult=None):
        score = Fraction(1)
        cur = list(pre)
        touched = False
        for x in seq:
            row = row_of(table, cur)
            if row is None:
                return None, False
            w = dict(row).get(x)
            if w is None:
                return None, False
            f = w
            if mult_key is not None and tuple(cur) == mult_key[0] \
                    and x == mult_key[1]:
                f *= mult
                touched = True
            score *= f
            cur = cur + [x]
        return score, touched

    rng = random.Random(seed + 4242)
    keys = []
    for pre in table:
        for tok, _ in table[pre]:
            keys.append((pre, tok))
    trials = 0
    cone_exact = 0
    cone_total = 0
    factor_exact = 0
    factor_total = 0
    changed_answers = 0
    total_answers = 0
    for _ in range(50):
        key = rng.choice(keys)
        mult = rng.choice([Fraction(2), Fraction(1, 2), Fraction(3)])
        trials += 1
        for pre in queries:
            oracle, _ = completes_within(table, pre, DEPTH - len(pre))
            base_best = None
            over_best = None
            for seq, _iscore in oracle:
                s0, _ = fscore(pre, seq)
                s1, touched = fscore(pre, seq, key, mult)
                if touched:
                    factor_total += 1
                    if s1 == s0 * mult:
                        factor_exact += 1
                else:
                    cone_total += 1
                    if s1 == s0:
                        cone_exact += 1
                if base_best is None or s0 > base_best[0]:
                    base_best = (s0, tuple(seq))
                if over_best is None or s1 > over_best[0]:
                    over_best = (s1, tuple(seq))
            total_answers += 1
            if base_best and over_best and base_best[1] != over_best[1]:
                changed_answers += 1
    return [f"### Edit locality battery (seed {seed})",
            f"single key overlay trials: {trials}",
            f"paths not touching the edited key: {cone_total}; "
            f"fraction score exactly unchanged: {cone_exact}",
            f"paths touching the edited key: {factor_total}; "
            f"score changed by exactly the multiplier: "
            f"{factor_exact}",
            f"certified style best answers changed: "
            f"{changed_answers} of {total_answers} (query, overlay) "
            f"pairs"]


def reweight_battery(seed):
    """Route one: axis scores. Candidates are the complete
    paths from the root of a second fixture; each candidate
    carries four features; its support is the axes with a
    nonzero feature. Two checks over random weightings and
    random single axis reweightings: the winner under any
    weighting is on the Pareto frontier of the feature
    vectors, and the incremental winner (rescore only the
    candidates whose support holds the changed axis) equals
    the full recomputation winner."""
    table = build_table(seed + 99)
    oracle, _ = completes_within(table, [], DEPTH)
    cands = []
    for seq, sc in oracle:
        feats = [sc,
                 sum(1 for t in seq if t > 11),
                 sum(1 for t in seq if t <= 11),
                 1 if seq[0] % 2 == 0 else 0]
        support = [i for i, f in enumerate(feats) if f != 0]
        cands.append({"seq": tuple(seq), "feats": feats,
                      "support": support})

    def winner(w, subset=None):
        pool = cands if subset is None else subset
        best = None
        for c in pool:
            s = sum(w[a] * c["feats"][a] for a in c["support"])
            if best is None or s > best[0]:
                best = (s, c["seq"])
        return best

    def dominated(c):
        for d in cands:
            if d is c:
                continue
            if all(d["feats"][i] >= c["feats"][i] for i in range(4)) \
                    and any(d["feats"][i] > c["feats"][i]
                            for i in range(4)):
                return True
        return False

    frontier = [c for c in cands if not dominated(c)]
    rng = random.Random(seed + 31337)
    winner_on_frontier = 0
    trials = 300
    selected = set()
    for _ in range(trials):
        w = [rng.randint(1, 9) for _ in range(4)]
        win = winner(w)
        selected.add(win[1])
        if any(c["seq"] == win[1] for c in frontier):
            winner_on_frontier += 1
    unselected = [c for c in frontier if c["seq"] not in selected]
    incr_ok = 0
    incr_trials = 300
    for _ in range(incr_trials):
        w = [rng.randint(1, 9) for _ in range(4)]
        axis = rng.randrange(4)
        w2 = list(w)
        w2[axis] = rng.randint(1, 9)
        full = winner(w2)
        affected = [c for c in cands if axis in c["support"]]
        kept = {}
        for c in cands:
            if axis not in c["support"]:
                kept[c["seq"]] = sum(w[a] * c["feats"][a]
                                     for a in c["support"])
        best = None
        for c in affected:
            s = sum(w2[a] * c["feats"][a] for a in c["support"])
            if best is None or s > best[0]:
                best = (s, c["seq"])
        for seq, s in kept.items():
            if best is None or s > best[0]:
                best = (s, seq)
        if best == full:
            incr_ok += 1
    return [f"### Axis reweighting battery (seed {seed})",
            f"candidates: {len(cands)}; Pareto frontier members: "
            f"{len(frontier)}",
            f"winners on the frontier: {winner_on_frontier} of "
            f"{trials} random weightings",
            f"frontier members no sampled weighting selected: "
            f"{len(unselected)} of {len(frontier)} (the weighting "
            f"cannot recover every frontier behavior; the count "
            f"is a sampled lower bound, printed as measured)",
            f"incremental winner equals full recomputation winner: "
            f"{incr_ok} of {incr_trials} random single axis "
            f"reweightings"]


def classification_battery(seed):
    """Classification: the label of a length two prefix is the
    parity of the first token of its best completion. The
    certified classifier answers only where certified, at the
    oracle's label by construction; the sampled classifier
    votes over five samples and answers everywhere. The trade
    printed is coverage against accuracy."""
    table = build_table(seed)
    rng = random.Random(seed + 555)
    twos = [list(p) for p in table if len(p) == 2]
    cert_ans = 0
    cert_right = 0
    samp_right = 0
    total = 0
    for pre in twos:
        oracle, _ = completes_within(table, pre, DEPTH - len(pre))
        if not oracle:
            continue
        total += 1
        best = max(oracle, key=lambda z: z[1])
        label = (pre + best[0])[0] % 2
        cert = certified_decode(table, pre, DEPTH - len(pre))
        if cert["certified"]:
            cert_ans += 1
            got = (pre + cert["answer"])[0] % 2
            if got == label:
                cert_right += 1
        votes = []
        for _ in range(5):
            r = sampled_decode(table, pre, 1.0, rng, DEPTH - len(pre))
            if r["answer"]:
                votes.append((pre + r["answer"])[0] % 2)
        if votes:
            vote = 1 if sum(votes) * 2 > len(votes) else 0
            if vote == label:
                samp_right += 1
    return [f"### Classification battery (seed {seed})",
            f"classifiable prefixes: {total}",
            f"certified classifier: answered {cert_ans}, correct "
            f"{cert_right} (coverage "
            f"{cert_ans / total:.3f}, accuracy on answered "
            f"{(cert_right / cert_ans if cert_ans else 0):.3f})",
            f"sampled vote classifier: accuracy {samp_right} of "
            f"{total} ({samp_right / total:.3f}) at full coverage"]


def main():
    out = []
    out.append("# Empirical results — fixture scale")
    out.append("")
    out.append("Fixture: synthetic archived row tables built on "
               "this machine by build_table(seed): vocabulary 24, "
               "completeness at length three, rows present with "
               "probability 0.9 per prefix (missing rows are the "
               "unresolved branches), raw weights 1..9 normalized "
               "to probability rows (weight over row sum), so a "
               "path score is a product of fractions and a "
               "prefix's score bounds its completions — the "
               "premise the certification rule stands on. "
               "Checkpoint name synthetic-1, protocol "
               "prlm-fixture-1. Every number below is from these "
               "fixtures; nothing here is a real checkpoint "
               "measurement.")
    out.append("")
    for seed, label in ((11, "development seed 11"),
                        (23, "held out seed 23")):
        rows = serving_battery(seed)
        out += summarize(rows, label)
        out.append("")
    out += overlay_battery(11)
    out.append("")
    out += reweight_battery(11)
    out.append("")
    out += classification_battery(11)
    out.append("")
    out.append("## Unmeasured cells, with the blocker named")
    out.append("")
    out.append("- Real checkpoint cells (the Pythia class "
               "fixtures of the deterministic decoding line): "
               "UNMEASURED. Blocker: the standalone fixture "
               "repo is not on this machine and no route to it "
               "exists from here; relaying side access, on "
               "record since 2026-11-19.")
    out.append("- Code generation beyond fixture scale: "
               "UNMEASURED. The fixture's sequences stand for "
               "token continuations generally; no code corpus "
               "or code model is on this machine.")
    out.append("- Live serving latency and throughput: "
               "UNMEASURED. No serving stack runs on this "
               "machine; costs here are counted operations "
               "(row lookups and heap pops), not wall clock.")
    out.append("- Extraction against a real archived model: "
               "UNMEASURED, same fixture blocker as the real "
               "checkpoint cells. At fixture scale extraction "
               "is the serving battery's certified agreement "
               "with the exhaustive oracle.")
    with open("results.md", "w") as f:
        f.write("\n".join(out) + "\n")
    print("\n".join(out))


if __name__ == "__main__":
    main()
