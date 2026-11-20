# Specification — the parametric rewritable language model

State of this document: settled intent for the definitions and
contracts; implemented behavior only where the proof folder or
the harness folder of this repo carries it; verified behavior
only where the family gate or a recorded run at a named pin
says so. The claim map is census.md; no sentence in this
document upgrades a claim past the state census.md gives it.

## 1. The object

A parametric rewritable language model is a pair (table,
parameters) whose behavior — the action stream it produces for
a content — is a totally deterministic function of the content
and the parameters together. There is no sampling anywhere in
the model. Randomness, where a deployment wants variety, is a
parameter (a named seed axis, section 3), never a hidden
mechanism.

The parameters are meaningful: every parameter is named, typed,
and carries an effect contract a person can read before tuning
it (section 3). No parameter is an opaque coordinate of a
weight vector. Behavior is tailored to content by rewriting
parameters (section 4), incrementally and reversibly, never by
retraining the table and never by re-rolling dice.

The totally deterministic path — generation by the certified
best-first rule of section 5 over the table — is the
feed-forward deterministic language model: feed the content
forward through the table under the parameters; the output is
the certified optimum of the stated objective, or a named
refusal where certification is impossible.

## 2. Content, rows, and the table

- A token is an element of a finite vocabulary. In the proof
  core a token is a natural number; in the harness the
  vocabulary is the fixture's word list.
- A prefix is a finite token sequence. The empty prefix is the
  root.
- A row is the recorded next-token distribution at one prefix:
  a finite list of (token, weight) pairs, weights positive
  rationals, no token repeated. A row is evidence: it was
  produced by a named checkpoint under a named protocol.
- The table is the finite set of recorded rows, keyed by
  prefix. A prefix with no recorded row is missing, and missing
  is a state, never a zero: section 5 carries a missing row's
  prefix as an unresolved branch.
- Every behavioral quantity is keyed by prefix + token +
  checkpoint + protocol, never by token alone (the keying
  discipline of the tensor-edit control surface, Chris, direct,
  2026-11-19 20:28 PST).

## 3. The parameter space

A parameter assignment is a tuple of the following named
components. Each component lists its type, its meaning, and
its effect contract — what a change to it may and may not do.

1. route — one of {certified, frontier}. Meaning: how the
   action is determined. certified: the feed-forward
   deterministic path of section 5. frontier: the candidate set
   is computed weight-free, its Pareto frontier extracted, and
   only then may weights select (frontier before weights; the
   weighting cannot recover every frontier member — the proved
   counterexample class is cited in census.md, not re-proved).
   Effect contract: changing route changes the determination
   procedure, never the table and never the objective's axes.
2. axes — a finite list of named objective axes. Each axis is a
   named, legible feature of a candidate (for decoding: length,
   rarity, and the like; for action determination: the semantic
   axes of the candidate-space program). Effect contract: an
   axis is a function from candidates to rationals, stated in
   the open; an axis with no stated function is not an axis.
3. weights — one positive rational per axis in axes. Meaning:
   the deliberate trade-off among axes, chosen by a person or
   by the meta-search over weighting configurations. Effect
   contract: weights select among frontier members only; a
   weight change affects exactly the derivations whose premise
   cone contains a changed axis (the locality theorem of the
   proof core).
4. overlay — a finite list of token edits, at most one per key.
   Each edit names a key (prefix, token), a positive rational
   multiplier, and the checkpoint and protocol it was recorded
   under. Meaning: route two of the reweighting discipline —
   change how tokens are weighted at selected recorded
   prefixes. Effect contract: applying an overlay multiplies
   the named tokens' weights by their multipliers and
   renormalizes each touched row (divides the row by its new
   sum); renormalization scales every path through a touched
   row by that row's one constant, so within-row order is
   preserved exactly. Removing an overlay — applying its
   pointwise inverse — restores the original weights exactly.
5. threshold — a rational, written τ. Meaning: the
   acceptability face of the stop rule. Effect contract: a
   threshold can make a candidate acceptable; it can never make
   it optimal. An optimality claim requires the certification
   face of section 5 (the two-face rule; the threshold control
   stands refuted in clpi/software-is-reversible).
6. bound — a natural number: the maximum sequence length the
   decoder enumerates. Effect contract: completeness and
   certification are stated relative to the bound; a claim past
   the bound is not made.
7. tiebreak — the enumeration order on candidates. Meaning:
   among score-equal optima, the first in tiebreak order is
   the answer. Effect contract: tiebreak is part of the
   parameters precisely so that determinism never rests on an
   unstated convention.

A seed axis may be added to axes by the rewriting operations;
it is an ordinary axis whose feature is a stated hash of the
content, and it is the only sanctioned source of variety.

## 4. The rewriting operations

Each operation is a function from parameter assignments to
parameter assignments, with its cone: the set of parameter keys
whose change can affect a derivation.

- addaxis / dropaxis: extend or shrink axes (weights extended
  or restricted to match). Cone: the axis named.
- reweight: replace one axis's weight. Cone: that axis.
- edit: add one token edit to overlay, refusing a second edit
  at a key that already carries one (a key carries one edit or
  none; composing two intended changes at one key is a new edit
  with the product multiplier, recorded as its own entry).
  Cone: the edit's key, and every derivation whose path passes
  through that key.
- unedit: remove the edit at a key; equal to applying the
  pointwise inverse overlay. Cone: as edit.
- setroute, setthreshold, setbound, settiebreak: replace the
  named component. Cones: the determination procedure, the
  acceptability face, the enumeration depth, the tie order,
  respectively.

Rewriting is incremental: an operation touches its cone and
nothing else, and every derivation outside the cone is
bit-identical before and after (proved for the axis cone in
the proof core; the overlay cone form is a named premise with
its gap owned, census.md). Rewriting is monotone in the
program's sense: a rewrite appends a new parameter epoch; the
prior epoch is never mutated, and any earlier behavior is
reproducible by naming its epoch.

## 5. The feed-forward deterministic path

Input: a content (a starting prefix), the table, and a
parameter assignment with route = certified. A completeness
rule, named in the deployment, decides which prefixes are
complete answers.

1. A max-heap of frontier entries, ordered by score, seeded
   with the starting prefix at score 1. An entry is a prefix
   together with its score: the product of the (possibly
   overlay-adjusted, renormalized) token weights along its
   path.
2. Pop the highest entry. If it is complete, it is the answer:
   nothing left in the heap can beat it, because every heap
   entry scores at most the popped score and a completion never
   exceeds its own prefix's score (probability factors are at
   most 1 — the bound premise, census.md P-bound, stated here
   as part of the rule exactly as its author stated it).
3. If it is not complete and its row is recorded, push every
   legal next token, scored prefix score times token weight.
4. If its row is missing, the entry leaves the heap as an
   unresolved branch carrying its score as an upper bound. It
   is never silently dropped and never scored zero.
5. Certification (the offline face): keep the best complete
   answer found. Certify it only once its score beats or ties
   both the heap maximum and every unresolved bound. Until
   then the state is named: best-so-far, uncertified, with the
   blocking bounds listed. The queues save and resume when rows
   are added; adding rows is an append, and a resumed run's
   certificate is a certificate for the enlarged table, stated
   as such.

Determinism contract: same content, same table, same parameter
assignment — including tiebreak — give the same action stream,
always. There is no other input. (Proved in the proof core as
uniqueness of the selected answer under the selection
specification.)

## 6. Where it claims to win

Each claim is a contract: same fixture, same task set, for
every rival; the axes are reproducibility (distinct outputs
across repeated identical queries), certification (whether the
engine can certify its answer optimal, and the score gap where
it cannot), cost per certified answer (expansions and row
lookups per certificate), edit locality (derivations changed
outside a rewrite's cone: zero by contract, measured), and tail
behavior (the worst score gap observed across repeats). The
rivals are ordinary sampled serving at stated temperatures and
the greedy deterministic baseline. The empirical state of every
claim is in census.md; the harness of this repo is the executed
evidence at fixture scale, and the real-checkpoint cells are
UNMEASURED with their blocker named until the
deterministic-llms fixtures are on this machine. No benchmark
gaming: no tuning to the test set, no contract narrowing,
held-out tasks validate the down-selection, losses print as
losses.

## 7. The compression horizon

Proposed, not implemented — stated at exactly this strength.
The table plus parameters are data; the decoder is a fixed,
small interpreter. By the minimum-representation results of
clpi/software-persistence-is-minimal at
eb01cf2e33a20bfbda5a03aba7a48c70fbd10741, a persistent state
carries a minimum representation, and the restart-records
corpus measured an encoding at 0.405414 of its stored size
(stored size witnessed not minimum). The horizon claim: a
model in this paradigm is executable compressed bytes — the
minimum representation of its table and parameter epochs, run
by the decoder directly, with no decompression to an obscure
weight vector anywhere in the path. What is missing: a
minimum-representation producer for row tables, the
executable-bytes format, and a same-contract measurement of
the pair against a checkpoint of equal behavior. Each is a
named item in census.md with an owner. Nothing in sections
1–6 depends on this horizon.

## 8. The hypergraph

Parameters, epochs, rewrites, theorems, and empirical verdicts
of this program are terms and records of the one append-only
hypergraph (the construction of 2026-11-19 15:43 PST: the
singular total equivalence terms graph). This repo carries the
program's extract in the canonical registry's term form
(extract.json, hypergraph.md); appending it into the canonical
registry of clpi/software-redundancy-is-equivalence is a named
item in census.md with its route and owner.
