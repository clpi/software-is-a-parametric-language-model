# software-is-a-parametric-language-model

A language model whose behavior is a totally deterministic
function of (content, parameters), where the parameters are
meaningful — named, legible axes a person tunes deliberately
— never an obscure weight vector; rewritable incrementally
and parametrically, so behavior is tailored to content needs
by rewriting parameters, not by retraining or sampling. The
totally deterministic path — generation by the certified
best first rule, no sampling anywhere — is the feed forward
deterministic language model.

This is the constructive counterpart of the obscure weights
line: decompiling obscure weights into semantic meaning is
how an existing model becomes one of these.

## Contents

- spec.md — the object, defined at agent proof resolution:
  the content, the parameter space with each parameter's
  meaning and effect contract, the rewriting operations with
  their cones, the feed forward deterministic path and its
  certification rule, where the paradigm claims to win, the
  compression horizon, and the hypergraph section.
- proof/ — the Lean core: 40 theorems (fraction arithmetic,
  the selection machinery, the decoder and its determinism,
  certification soundness and blocking, the overlay round
  trip and cone invariance, route one locality, two standing
  controls). The family gate: proof/check.sh, cold, Lean
  4.19.0, warnings as errors, escape scan, dependency audit
  inside {propext, Classical.choice, Quot.sound}. Gate
  verdict at founding: PASS (proof/CHECK.log).
- harness/ — the empirical program at fixture scale:
  run.py builds synthetic probability row tables on this
  machine and runs the serving, edit locality, axis
  reweighting, and classification batteries on two seeds,
  one held out; results.md carries the numbers and the
  unmeasured cells with their blockers.
- census.md — every claim of the program at its evidence:
  proved here, proved by citation at pins, premises named,
  measured, unmeasured.
- extract.json and hypergraph.md — the program's terms in
  the canonical hypergraph's registry form, and the owned
  append item.

## Headline results

- Determinism is a theorem: the decoder's answer is the
  unique satisfier of its specification.
- Certification is sound under its named coverage premise,
  and its blocking direction is proved outright; at fixture
  scale the certified score equals the exhaustive oracle
  maximum on every certified query, on both seeds.
- Rewriting is exact: an overlay applied and removed
  restores every weight and every path score (proved), and
  at fixture scale 37,964 of 37,964 paths outside an edit's
  cone keep their fraction score exactly.
- A weighting cannot recover every Pareto optimal behavior:
  the counterexample class stands proved in
  clpi/software-is-reversible and is measured again here
  (3 of 5 frontier members selected by no sampled weighting).
- The real checkpoint cells are UNMEASURED: the standalone
  fixture repo is not on this machine. Nothing in this repo
  is a real checkpoint measurement.
