#!/usr/bin/env python3
"""System 2: incremental certified best-first synthesis over archived rows.

Wraps the parametric language model harness's decoder unmodified
(software-is-a-parametric-language-model, harness/run.py at ca4ca2b):
certified_decode reads the table only through table.get, via row_of.
A TrackedTable records every key looked up, including keys that return
no row (a missing row is a premise: adding it can change the verdict),
with a hash of what was seen. That key -> hash map is the query's cone.

Rule (SPEC.md, system 2): the decoder's run is a function of the values
returned by its lookups (heap order, tie counter and the break condition
read nothing else), so a query whose cone hashes all still match the
edited table has the same verdict. An overlay edit at one row key
re-derives exactly the queries whose cones hold that key and saw a different
value there (an edit that leaves the row's hash unchanged is cut off early:
run_cone applies with the edited key inside the cone); every carried
verdict is admitted only after every cone hash is re-checked against the
edited table (asserted in the carry path). The checker is the original
decoder run whole on the edited table.

Unit of carried state: a distinct (prefix, bound) query. The harness's
query list repeats the root prefix; repeats share one verdict, and the
counts below say both numbers.
"""
from __future__ import annotations

import hashlib
import importlib.util
import os
from fractions import Fraction

MISSING = "missing"


def load_harness(path):
    spec = importlib.util.spec_from_file_location("prlm_run", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def row_hash(row):
    if row is None:
        return MISSING
    return hashlib.sha256(repr([(t, str(w)) for t, w in row]).encode()).hexdigest()[:16]


class TrackedTable(dict):
    """A dict whose get() records the cone of the current derivation."""

    def __init__(self, *a, drop_missing_mutant=False, **k):
        super().__init__(*a, **k)
        self.cone = None
        self._mutant = drop_missing_mutant

    def get(self, key, default=None):
        row = super().get(key, default)
        if self.cone is not None:
            if row is None and self._mutant:
                pass  # MUTANT: missing-row lookups are not premises
            else:
                self.cone[key] = row_hash(row)
        return row


class Engine:
    def __init__(self, harness, table, queries, drop_missing_mutant=False):
        self.h = harness
        self.table = TrackedTable(table, drop_missing_mutant=drop_missing_mutant)
        self.depth = harness.DEPTH
        self.keys = []
        for pre in queries:
            k = (tuple(pre), self.depth - len(pre))
            if k not in self.keys:
                self.keys.append(k)
        self.state = {}      # query key -> (verdict, cone)
        self.lookups = 0     # decoder lookups performed by this engine
        self.rederived = []  # query keys re-derived at the last edit
        self.carried = []

    def _derive(self, qk):
        pre, bound = qk
        self.table.cone = {}
        v = self.h.certified_decode(self.table, list(pre), bound)
        cone, self.table.cone = self.table.cone, None
        self.lookups += v["cost"]["lookups"]
        self.state[qk] = (v, cone)

    def build(self):
        for qk in self.keys:
            self._derive(qk)

    def edit(self, row_key, new_row):
        """Overlay edit at one row key: new_row replaces the row (None removes it)."""
        if new_row is None:
            dict.pop(self.table, row_key, None)
        else:
            dict.__setitem__(self.table, row_key, new_row)
        before = self.lookups
        self.rederived, self.carried = [], []
        for qk in self.keys:
            _v, cone = self.state[qk]
            if row_key in cone and cone[row_key] == row_hash(dict.get(self.table, row_key)):
                pass  # early cutoff: the key's value is what the cone saw (run_cone), carry below
            if row_key in cone and cone[row_key] != row_hash(dict.get(self.table, row_key)):
                self._derive(qk)
                self.rederived.append(qk)
            else:
                # carry: every premise hash must still match the edited table
                for k, hsh in cone.items():
                    assert row_hash(dict.get(self.table, k)) == hsh, (qk, k)
                self.carried.append(qk)
        return self.lookups - before

    def verdict(self, qk):
        v = self.state[qk][0]
        return (tuple(v["answer"]) if v["answer"] is not None else None,
                v["certified"], v["score"], v["blocking"])


def scratch(harness, table, keys):
    """Checker: the original decoder run whole on a plain dict copy."""
    plain = dict(table)
    out, lookups = {}, 0
    for pre, bound in keys:
        v = harness.certified_decode(plain, list(pre), bound)
        lookups += v["cost"]["lookups"]
        out[(pre, bound)] = (tuple(v["answer"]) if v["answer"] is not None else None,
                             v["certified"], v["score"], v["blocking"])
    return out, lookups


def overlay(row, tok, mult):
    """The harness's overlay: one entry of one row scaled by mult."""
    return [(t, w * mult if t == tok else w) for t, w in row]
