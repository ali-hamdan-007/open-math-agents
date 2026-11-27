# Publication manifest for the adjacent R2-H2 family

The target is the normalized R2-H2 family of ray heights $(h+1,h,h+1,h)$. The Lean theorem `OMA.GreenR2Adjacent.normalized_adjacent_iff` identifies its six normalized members. The theorem `OMA.GreenR2Adjacent.r2_h2_adjacent_heights_complete` rules them all out under the exact no-red-triple, shorter-step hitting, and fixed-ray premises of R2-H2. Thus it settles six fibers of R2-H2, including the previously unchecked edge $h=0$. The other normalized R2-H2 fibers and the full upper bound remain outside the claim.

## Preserve these relative paths

Start at `parallel/ramsey`. Include text files only. The build needs Lean 4.33.1 and works without Mathlib.

| Files | Purpose |
| --- | --- |
| `Green160NearWitness.lean` | Shared checker template and 160-point progression definitions. |
| `window141/Green130WindowCore.lean`, `window141/Green130Window64.lean`, `window141/Green130R2Bridge.lean` | Existing proof of $h=4,5$. |
| `r2adjacent/Green137WindowCore.lean`, `r2adjacent/Green137Window27.lean`, `r2adjacent/Green150WindowCore.lean`, `r2adjacent/Green150Window14.lean`, `r2adjacent/GreenR2Adjacent.lean` | Existing checked proof of $h=1,2,3,4,5$. |
| `r2adjacent/edge154/Green154EdgeCore.lean`, `r2adjacent/edge154/Green154EdgeChunk00.lean` through `Green154EdgeChunk09.lean`, `r2adjacent/edge154/Green154EdgeSeed.lean` | Width-154 certificate for $h=0$. |
| `r2adjacent/GreenR2AdjacentFull.lean` | Exact normalization and universal six-case result. |
| `r2adjacent/verify_full.sh`, `r2adjacent/edge154/verify.sh` | Sequential verification with a temporary output directory. |
| `search160.cpp`, `r2adjacent/make_window.py`, `r2adjacent/window.tail`, `r2adjacent/edge154/generate.py` | Regenerate the checked tapes. |
| `r2adjacent/README.md`, `r2adjacent/edge154/PUBLICATION.md`, `r2adjacent/edge154/search.log`, `r2adjacent/edge154/lean.log`, `r2adjacent/edge154/final-audit.log` | Build instructions, scope, and audits. |

From that directory, verify all modules sequentially:

```sh
r2adjacent/verify_full.sh
```

Set `LEAN_BIN` if Lean 4.33.1 is outside `PATH`. The edge-only build command accepts an output directory containing the earlier `Green160NearWitness.olean` dependency when passed explicitly.

## Regenerate the new edge proof

```sh
sed 's/++calls>=100000/++calls>=800000/' search160.cpp > /tmp/green-edge-search.cpp
g++ -std=c++17 -O3 /tmp/green-edge-search.cpp -o /tmp/green-edge-search
python3 r2adjacent/edge154/generate.py /tmp/green-edge-search
```

The search uses a 154-point window with fixed red positions $(1,3,13,15)$. It finds 882 certificate fragments across 127,771 nodes. The generator checks that each fragment only references earlier fragments, splits the source into 10 bounded tape modules, and emits a short final bridge. Lean checks each fragment using `decide +kernel`. Publish the modules separately to keep the verification memory bounded.

Once the audit logs are present, `r2adjacent/edge154/package.sh` creates the reproducible text-only archive `Green14-W3-13-R2-adjacent.tar.gz`. Pass a different path as its first argument to rename the archive.
