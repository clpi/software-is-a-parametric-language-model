# Incremental recomputation: certified best-first synthesis

The harness decoder (../run.py, certified_decode, unmodified) under a table
that records every key it reads, including keys with no row (a missing row is
a premise), with a hash of what it saw. That map is the query's cone. An edit
at one row key re-derives exactly the queries whose cones hold it; every
other verdict carries only after its cone hashes are re-checked against the
edited table (asserted). The checker is the decoder run whole.

Resume: an affected query restarts at the checkpoint taken just before its
first read of the edited key (ResumeEngine, a replica decoder that records
heap, tie counter, unresolved bounds, best and cost before each read; the
original decoder checks every result). Seed 11, 316 single-key edits: 1,863
lookups resumed vs 3,322 whole-query vs 13,718 from scratch; seed 23: 1,251 vs
2,325 vs 7,944. An edit that leaves a row's value unchanged re-derives nothing.

Run: `python3 -B harness/incremental/gate.py s2`.

Measured (counts, decoder lookups): seeds 11 and 23, every single-key edit and
its revert (294 and 212 edits, 5 of them insert a row where a cone saw none)
agree with the decoder run whole; each re-derives exactly its cone holders,
mean 1.86 of 15 and 1.84 of 14 distinct queries, max 3; 3,113 vs 12,784 and
2,167 vs 7,366 lookups. An edit no cone holds: 0 and 0. 60 chained edits with
state never reset agree after every edit. A mutant that drops missing-row keys
is caught. Lean (in clpi/software-redundant-compute-expands): run_cone,
edit_outside, missing_is_a_premise, resume; the premise that the decoder reads the
table only through get is observed, not proved.
