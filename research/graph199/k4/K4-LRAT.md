# Independently checkable CNF refutations for connectivity four

The 21 finite instances in the Graph 199 triangle-free connectivity-four
argument have DIMACS CNFs and LRAT refutations. Lean 4.33.1's executable
`Std.Tactic.BVDecide.LRAT.check` accepted all 21 refutations, checking
3,069,299 original clauses and 1,168,659 LRAT actions in total. The hardest
case, order 17 and independent-set overlap 2 with the marked pentagon,
uses 508,534 clauses and 753,470 LRAT actions.

`K4LratCheck.lean` parses the DIMACS and invokes the standard LRAT checker.
Its soundness theorem `Std.Tactic.BVDecide.LRAT.check_sound` was checked by
Lean and uses only `propext`, `Classical.choice`, and `Quot.sound`. The
certificate replay runs the executable checker. The graph-to-CNF
correspondence and analytic order bounds remain mathematical arguments.

## Encoding

The source SMT instances and their graph meanings are described in
`k4-classification.md`. `cnf_k4.py` translates these complete instances,
including the audited learned tree clauses, independently of any solver.
It introduces one Boolean variable per marked edge and fixes variable 1
to true. Negation is represented by switching the literal sign. For a
disjunction of literals, the Tseitin variable is forced to be equivalent
to that disjunction. Conjunction follows by De Morgan duality, while
implication and equality use their truth-functional definitions. A
threshold of at least k true among a prefix is equivalent to at least k
among its shorter prefix, or the last literal being true and at least
k−1 among that shorter prefix. The at-most constraints negate the next
at-least threshold. Thus any assignment of edge variables satisfying the
graph constraints extends to a satisfying CNF assignment by assigning
all Tseitin variables their formula values. Conversely, the equivalences
make the edge-variable projection of any CNF solution satisfy the source
instance. Positive top-level disjunctions become clauses directly.

The source SMT checker `audit_finite_k4.py` compares the base clauses
against their generators and independently confirms that all learned
obstructions are induced trees on seven vertices. That script uses Z3 to
replay the SMT, but Z3 is unnecessary to replay the LRAT proofs.

## Reproduction

Run the following from the extracted directory with the Lean 4.33.1
toolchain on PATH.

```sh
lean --run K4LratCheck.lean k4-17-2.cnf k4-17-2.lrat
```

To check every case with failure status on any rejected certificate:

```sh
set -e
for cnf in k4-*.cnf; do
  lean --run K4LratCheck.lean "$cnf" "${cnf%.cnf}.lrat"
done
```

To regenerate a DIMACS input, run `python3 cnf_k4.py k4-17-2.smt2`.
To independently generate a new refutation, run
`cadical --lrat k4-17-2.cnf new.lrat`. CaDiCaL 2.1.2 as bundled with
Lean 4.33.1 emitted an empty trace for case 11-1, which was
unit-inconsistent while parsing. `unit_lrat.py` provided the portable
one-step LRAT certificate for that case. The same Lean checker
verified it.

For a source-only checkout, first unpack the existing
`graph199-k4-certificate.tar.gz` into a fresh input directory. Then run

```sh
./replay_k4_lrat.sh /path/to/extracted-input /path/to/new-output
```

The replay script accepts `K4_LEAN`, `K4_CADICAL`, and `K4_JOBS` overrides.
It verifies the original SMT checksums and the regenerated DIMACS checksums.
`k4-lrat-original.sha256` records the original proof byte hashes for
provenance. Replay accepts a different valid proof from a different solver
version because Lean checks the proof against the same DIMACS. The aggregate
original verification log is `k4-lrat-verification.log`.
