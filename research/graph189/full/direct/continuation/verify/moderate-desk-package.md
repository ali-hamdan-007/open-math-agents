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

The generated reduction and four preliminary leaf files passed the official static linter. The reduction also passed the local pinned checker with the exact focused target. Official single-file kernel replays and official acceptance are separate milestones.

The four proof-body manifests from the [independent Linux job](https://github.com/ali-hamdan-007/open-math-agents/actions/runs/46138454950/job/140958894706) are in [moderate-leaf-manifests.tar.gz](moderate-leaf-manifests.tar.gz). Extract the archive in a fresh directory and pass its path with `--dependencies`. The original and specialized H1 and all four exact helper types passed the pinned kernel.
