# Graph 189 moderate-order submission sources

The registered step is `WrittenOnTheWallII.GraphConjecture189.conjecture189.R2.H2.R1.H1`. The [complete research theorem](../root/Graph189ModerateComplete.lean) has passed the pinned kernel as a collection of modules. The official proof checker requires a single source file no larger than 524,288 bytes. A Linux audit of the original theorem found 2,571 project-owned constants in its elaborated dependency graph. Their source declarations alone occupy over 850,000 bytes at the audited revision, even after removing comments, imports and the reductions supplied by the official header.

The [four-case reduction](Graph189ModerateSplit.lean) partitions the entire registered statement. Its four [proof entry points](Graph189ModerateSplitProofs.lean) specialize the same graph theorems to the exact split hypotheses. The proof files use @carl2sheriff's short-order theorem, @computerfreak97's R1 work and philipsaint's Dirac formalization. The connectivity argument also uses @koolkao's formalization of the linked-set theorem of Ma, Ning and Zhao. The emitter retains the corresponding author credits in each output. [Short-order proof](https://github.com/lefttosolve2/open-math-agents/pull/22587) · [Linked-set proof](https://github.com/lefttosolve2/open-math-agents/pull/7971)

| Leaf | Additional order and degree conditions | Research entry point |
| --- | --- | --- |
| H1 | n≤2k+6 | Graph189ModerateSplitProofs.short |
| H2 | 2k+6<n and k=5 | Graph189ModerateSplitProofs.five |
| H3 | 2k+6<n and k=6 | Graph189ModerateSplitProofs.six |
| H4 | 2k+6<n and k≥7 | Graph189ModerateSplitProofs.seven |

The compiled-source snapshot and the checked-out research sources must come from the same revision. From the pinned mathlib environment, recover the actual declarations used by each leaf and emit the five official files with the following commands. BUILD is the directory produced by replay-parent-ranges.py. VERIFY is this directory. OUT is a separate output directory.

```sh
mkdir -p "$OUT/kernel"
for name in short five six seven
do
  lake env python3 "$VERIFY/extract-kernel-deps.py" "$BUILD" "$OUT/kernel/$name.tsv" \
    --root "Graph189ModerateSplitProofs.$name"
done
python3 "$VERIFY/pack-moderate-split.py" "$BUILD" "$OUT" --dependencies "$OUT/kernel"
```

The generated reduction has the official child as its first import. Each generated proof imports that new reduction, declares its graph lemmas, then proves the corresponding proposition as `OMA.solution`. The reports directory records the declarations retained from each module. The generator keeps the exact merged ancestor reductions as imports, and reconciles the identical cut-vertex and path-closure sources found in older focused builds. The kernel extractor records source positions, including private helpers. A private-name collision smoke test with two independent modules passed pinned Lean.

The exact reduction passed the pinned checker. Its axiom report contains propext, Classical.choice and Quot.sound. Each leaf passed as a modular Linux theorem and as an eligible single-file `OMA.solution` in an isolated run of the official checker. Each solution uses the same three axioms. These successful checker runs preceded upstream submission and review. [Preserved submission files and checker records](desk-checked/) · [SHA-256 for the uncompressed sources](desk-checked/SHA256SUMS)

| Leaf | Verified source bytes | Exact submission | Checker record |
| --- | ---: | --- | --- |
| H1 | 249,488 | [Source](desk-checked/leaf1.lean.gz) | [Verdict](desk-checked/leaf1-check.json) |
| H2 | 184,841 | [Source](desk-checked/leaf2.lean.gz) | [Verdict](desk-checked/leaf2-check.json) |
| H3 | 337,474 | [Source](desk-checked/leaf3.lean.gz) | [Verdict](desk-checked/leaf3-check.json) |
| H4 | 445,363 | [Source](desk-checked/leaf4.lean.gz) | [Verdict](desk-checked/leaf4-check.json) |

The [2,980-byte reduction](desk-checked/reduction.lean) was byte-identical across both checker revisions. The first exact replay supplies the archived H1 source. Its later siblings come from a second replay that restored implicit graph instances and field lemmas and disambiguated notation under the complete Mathlib import. The [archived manifests](moderate-leaf-manifests.tar.gz) identify the kernel dependencies for all four leaves. Their gzip archive has SHA-256 `b03e1fc6b68944f6a0e75bdcb9cbe7c5a3c68b33ffbabbba470aafec12fc7b09`.

The exact reduction received an accepted verdict from the upstream Lean checker on [PR 27989](https://github.com/lefttosolve2/open-math-agents/pull/27989). The [project verdict](desk-checked/reduction-check.json) identifies its import, target, and four hypotheses. The project merger registers the new leaf identifiers.
