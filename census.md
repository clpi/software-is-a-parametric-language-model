# Census — every claim of the program, at its evidence

Four states, never blurred: proved (a gate run at a pin),
measured (a battery at a stated contract), premise (named,
with its falsification route), unmeasured (printed, with the
blocker named). A refuted claim stands as its control.

## Proved in this repo

The Lean core (proof/Prlm.lean, 40 theorems) passes the
family gate cold: Lean 4.19.0, warnings as errors, escape
scan clean, every printed dependency set inside
{propext, Classical.choice, Quot.sound}. proof/CHECK.log
carries the run; proof/Axioms.lean is the audit.

- Fraction arithmetic: equality and order by cross
  multiplication; reflexivity, symmetry, transitivity of
  equality (under positive denominators); order transitivity
  and compatibility; multiplication congruence; the unit
  laws; the inverse law; multiplication preserves order;
  associativity up to fraction equality.
- Selection: the champion of a list under a total preorder
  exists where the list is nonempty, is a member, is maximal,
  and is the first maximal member; the specification
  (member, maximal, first) has at most one satisfier.
- The decoder: appending distinct tokens is injective; the
  completion enumeration extends every enumerated completion
  by a suffix; the enumeration is duplicate free under row
  well formedness; the decoder's answer satisfies the
  specification where it answers; the answer is the unique
  satisfier of the specification (determinism).
- Certification: soundness — a certified answer's score is
  at least the score of every completion in the enumeration
  and at least every recorded frontier bound, under the
  coverage premise below; blocking — a frontier bound above
  the best complete score makes certification false, proved
  outright.
- The overlay: the inverse overlay's multiplier at a key is
  the inverse fraction; multipliers are positive where every
  recorded multiplier is; the round trip restores every
  weight and every path score exactly; the empty overlay
  changes no score; cone invariance — a path touching no
  edited key scores under the overlay exactly as on the
  recorded table.
- Route one: weightings agreeing on an axis list give equal
  scores over it; a reweighting at one axis leaves every
  score over a list excluding that axis exactly equal to its
  full recomputation.
- Standing controls, proved: greedy is not certified (on the
  control table greedy returns the completion scoring 9, the
  decoder returns the one scoring 45, by computation); an
  unresolved bound above the best complete score blocks
  certification.

## Proved by citation at pins — reused, not recomputed

- Frontier before weights, and the counterexample class (a
  frontier member no positive linear weighting selects):
  clpi/software-is-reversible at d05ff699511099e6b4b28b2ae50e5c7cd590507e,
  38 theorems, gate cold pass at that pin.
- The derivation to action pipeline: determinism of
  derivation, Pareto optimality of the selected action,
  incremental reevaluation equal to full on the covered cone,
  reversibility by append and compensating retraction, stop
  soundness in both faces — proved in the pipeline proof
  lane and landed into clpi/software-frontier-is-solvable
  (Pipeline module, 28 theorems; Worklist module, 51
  theorems; the repo at 206 theorems at the landing read).
  Record: ~/workspace/research/derivation-action-proof-2026-11-20.md.
- The closure worklist equals the least full closure at
  every append prefix, against the canonical view: the
  Worklist module above, and the canonical theory in
  clpi/software-redundancy-is-equivalence at
  37514fb71f76c6c0bb2ca41e4ec7d0d03b6ba9a (217 theorems).
- The threshold control (a threshold makes a plan
  acceptable, never optimal): clpi/software-is-reversible at
  the same pin.

## Premises, named

- P-bound (coverage): every completion beneath a frontier
  prefix scores at most the bound recorded for that prefix.
  Where rows are probability rows and the bound is the
  prefix's own score, the premise holds by construction
  (each further factor is at most one). For an arbitrary
  archived table it is a checkable condition on the table,
  and the certification theorem is stated under it, never
  without it. Falsification route: exhibit a table and a
  completion outscoring its prefix's recorded bound; the
  harness's first fixture draft did exactly this with raw
  weights, and the fixture was corrected to probability
  rows — the premise working as designed.
- The pipeline premises P1 to P6 (extraction fidelity,
  witness honesty, axis meaning, threshold choice, execution
  fidelity, progress) carry over to this paradigm unchanged;
  they are stated in the pipeline proof record at its pin.
  Axis meaning (P3) is the one this paradigm leans on
  hardest: an axis name is a definition, and where a name
  has no definition the parameter is refused, per the spec.

## Measured in this repo, fixture scale

harness/run.py over synthetic probability row tables built
on this machine (vocabulary 24, completeness at length
three, rows present with probability 0.9), development seed
11 and held out seed 23; full numbers in harness/results.md.

- Certified score equals the exhaustive oracle maximum on
  every certified query, both seeds. Certified rate 0.500
  and 0.524; the remainder are blocked by unresolved bounds
  and printed.
- Reproducibility: the certified and greedy engines return
  one output per query by construction and in every run;
  sampled serving returns 6.57 to 9.00 distinct outputs per
  query over 20 repeats.
- Tail: sampled worst score ratio to the best 0.024 to
  0.059 across batteries; greedy worst 0.533 to 0.611;
  certified ratio exactly 1 wherever it answers.
- Cost: certified mean 5.64 to 5.73 counted operations
  (lookups plus pops) per certified answer against greedy
  1.57 to 2.00 lookups — the certified path costs more per
  answer, printed as measured; what the extra cost buys is
  the certificate.
- Edit locality: 37,964 of 37,964 paths not touching an
  edited key keep their fraction score exactly; 986 of 986
  touching paths change by exactly the multiplier; the best
  answer changes in 51 of 1,100 (query, overlay) pairs.
- Route one: winners lie on the Pareto frontier in 300 of
  300 random weightings; the incremental winner equals the
  full recomputation winner in 300 of 300 single axis
  reweightings; 3 of 5 frontier members are selected by no
  sampled weighting (a sampled lower bound on the
  unrecoverable share, printed as measured).
- Classification at depth two prefixes: the certified
  classifier answers all 18, all correct; the sampled vote
  also answers all 18 correctly at this scale — no win
  claimed there beyond the guarantee itself.

## Unmeasured, with blockers

- Real checkpoint cells (the Pythia class fixtures of the
  deterministic decoding line): UNMEASURED. The standalone
  fixture repo is not on this machine; relaying side access
  blocker, on record since 2026-11-19. Owner: the fixture
  access route, when a file carrying channel delivers it.
- Code generation beyond fixture scale: UNMEASURED. No code
  corpus or code model is on this machine.
- Live serving latency and throughput: UNMEASURED. No
  serving stack runs on this machine; costs here are counted
  operations.
- The live demo chat surface's conformance to this spec:
  UNMEASURED here. The chat contract is the serving battery
  at fixture scale; the surface itself is another lane's
  build with labeled twin engines.
- The compression horizon (the model as executable
  compressed bytes): proposed, not implemented — see
  spec.md §7 and clpi/software-persistence-is-minimal at
  eb01cf2e33a20bfbda5a03aba7a48c70fbd10741.
- The canonical registry append of this repo's extract:
  owed; extract.json is the append ready form (see
  hypergraph.md). Owner: this program's follow on lane.
