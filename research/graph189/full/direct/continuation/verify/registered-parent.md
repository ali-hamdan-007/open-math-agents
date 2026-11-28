# Graph 189 verification

The registered theorem concerns a finite, nontrivial, connected simple graph. If the maximum number of vertices at even distance from any vertex is at most one plus the second-smallest degree, the graph has a Hamiltonian path. The starting vertex counts among its even-distance vertices. Degrees are counted with multiplicity.

The [original assembly](../root/bounded-order/Graph189Unconditional.lean) eliminates every possible counterexample. The [entry point](../root/bounded-order/Graph189OriginalSolution.lean) gives the proof the type of the registered theorem. At 15:19 UTC on 28 November 2026 the Linux runner built that registered module from Formal Conjectures commit `9097e2f90e66d2f6244209cb1c07f7120d17ec53`. Lean 4.33.1 reported the following result. [Build and kernel output](https://github.com/ali-hamdan-007/open-math-agents/actions/runs/46158940698/job/141021680430)

```text
'OMA.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The [successful workflow](https://github.com/ali-hamdan-007/open-math-agents/blob/994d7274dca16726f819dde6d3dc048f9c074187/.github/workflows/graph189-kernel-replay.yml) includes the complete environment setup. The graph sources are from [this research revision](https://github.com/ali-hamdan-007/open-math-agents/tree/9a5ab804/research/graph189). The matching mathlib commit is `0df444a360eaa60ab8c11dca51a86af692955474`. The following commands use absolute paths for the two pinned checkouts, the checkout of this research branch, and an output directory.

```bash
verify="$research/research/graph189/full/direct/continuation/verify"
(cd "$mathlib" && lake env python3 "$verify/replay-parent-ranges.py" \
  "$fc" "$build" Graph189Unconditional --modular-cut)
(cd "$fc" && bash "$verify/replay-registered.sh" "$build")
```

The replay generates the focused statement from the registered theorem's binders and compiles each research dependency. The second command builds the actual upstream import and elaborates the entry point against it. The upstream theorem's proof is never used.

## Single-file submission

The [dependency manifest](parent-kernel-declarations.tsv.gz) comes from traversing the types and values of constants starting at `Graph189FullProof.original`. It contains 8,834 research constants, including generated equations and instances. To regenerate the candidate with the syntax dependencies needed by the original proofs, run the following commands after the modular build.

```bash
mkdir -p "$out/proofs"
gzip -dc "$verify/parent-kernel-declarations.tsv.gz" > "$out/parent-deps.tsv"
python3 "$verify/pack-moderate.py" "$build" \
  "$out/proofs/WrittenOnTheWallII.GraphConjecture189.conjecture189.lean" \
  --original --dependencies "$out/parent-deps.tsv"
```

The exact single file in [upstream PR 34187](https://github.com/lefttosolve2/open-math-agents/pull/34187) passed the registered Lean statement guard and axiom audit in 12 minutes 18 seconds. The signed submission and the independently checked file have the same Git blob. The PR is ready for review. The upstream linter stopped at the default 512 KiB limit. The 2,707,845-byte proof passes that linter with the requested 3 MiB per-problem allowance in place. [Single-file kernel log](https://github.com/ali-hamdan-007/open-math-agents/actions/runs/46161071089/job/141028285846) The [verification record](parent-single-file-verification.json) gives the exact commits, proof digest, timings, and axiom report. The [size preflight](parent-size-preflight.json) records both results from the same upstream linter. Left to Solve lists the submission under `ali-hamdan-007`. [Account submission ledger](https://lefttosolve.com/api/pending?handle=ali-hamdan-007)

Ali Hamdan integrated the full argument and its graph formalizations. The proof reuses the short-order and longest-path work of carl2sheriff, the earlier metric and path work of computerfreak97, philipsaint's Dirac formalization, and koolkao's formalization of the linked-set argument of Ma, Ning and Zhao. The export preserves those source credits. [Short-order source](https://github.com/lefttosolve2/open-math-agents/pull/22587) · [Earlier path reduction](https://github.com/lefttosolve2/open-math-agents/pull/2971) · [Linked-set proof](https://github.com/lefttosolve2/open-math-agents/pull/7971)
