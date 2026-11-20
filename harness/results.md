# Empirical results — fixture scale

Fixture: synthetic archived row tables built on this machine by build_table(seed): vocabulary 24, completeness at length three, rows present with probability 0.9 per prefix (missing rows are the unresolved branches), raw weights 1..9 normalized to probability rows (weight over row sum), so a path score is a product of fractions and a prefix's score bounds its completions — the premise the certification rule stands on. Checkpoint name synthetic-1, protocol prlm-fixture-1. Every number below is from these fixtures; nothing here is a real checkpoint measurement.

### Serving battery (development seed 11)
queries: 22
certified rate: 0.500
certified score equals the exhaustive oracle maximum on every certified query: True
mean certified cost (lookups + pops) per certified answer: 5.636363636363637
greedy mean lookups: 2.00
greedy score ratio to the best, mean 0.963, worst 0.533
sampled T=1.0: distinct outputs per query over 20 repeats, mean 9.00, max 17; runs landing on the best completion: 93 of 440; worst score ratio to the best: 0.024
sampled T=0.7: distinct outputs per query over 20 repeats, mean 8.73, max 16; runs landing on the best completion: 107 of 440; worst score ratio to the best: 0.024
queries blocked by an unresolved bound: 11 of 22

### Serving battery (held out seed 23)
queries: 21
certified rate: 0.524
certified score equals the exhaustive oracle maximum on every certified query: True
mean certified cost (lookups + pops) per certified answer: 5.7272727272727275
greedy mean lookups: 1.57
greedy score ratio to the best, mean 0.946, worst 0.611
sampled T=1.0: distinct outputs per query over 20 repeats, mean 7.29, max 14; runs landing on the best completion: 125 of 420; worst score ratio to the best: 0.040
sampled T=0.7: distinct outputs per query over 20 repeats, mean 6.57, max 13; runs landing on the best completion: 131 of 420; worst score ratio to the best: 0.059
queries blocked by an unresolved bound: 9 of 21

### Edit locality battery (seed 11)
single key overlay trials: 50
paths not touching the edited key: 37964; fraction score exactly unchanged: 37964
paths touching the edited key: 986; score changed by exactly the multiplier: 986
certified style best answers changed: 51 of 1100 (query, overlay) pairs

### Axis reweighting battery (seed 11)
candidates: 76; Pareto frontier members: 5
winners on the frontier: 300 of 300 random weightings
frontier members no sampled weighting selected: 3 of 5 (the weighting cannot recover every frontier behavior; the count is a sampled lower bound, printed as measured)
incremental winner equals full recomputation winner: 300 of 300 random single axis reweightings

### Classification battery (seed 11)
classifiable prefixes: 18
certified classifier: answered 18, correct 18 (coverage 1.000, accuracy on answered 1.000)
sampled vote classifier: accuracy 18 of 18 (1.000) at full coverage

## Unmeasured cells, with the blocker named

- Real checkpoint cells (the Pythia class fixtures of the deterministic decoding line): UNMEASURED. Blocker: the standalone fixture repo is not on this machine and no route to it exists from here; relaying side access, on record since 2026-11-19.
- Code generation beyond fixture scale: UNMEASURED. The fixture's sequences stand for token continuations generally; no code corpus or code model is on this machine.
- Live serving latency and throughput: UNMEASURED. No serving stack runs on this machine; costs here are counted operations (row lookups and heap pops), not wall clock.
- Extraction against a real archived model: UNMEASURED, same fixture blocker as the real checkpoint cells. At fixture scale extraction is the serving battery's certified agreement with the exhaustive oracle.
