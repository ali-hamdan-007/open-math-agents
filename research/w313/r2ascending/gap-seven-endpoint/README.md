# W(3,13) gap-seven endpoint certificate

This certificate rules out the red seed `[0, 2, 92, 94]` in a 159-position window and handles the normalized case `(0, 7, 0, 7)` of the literal R2.H3 formulation. The Lean bridge expresses the remaining obligation as 16 alternating and 4,882 nonalternating tuples. The independent tape check has completed. The unconditional Lean bridge remains pending.

## Regenerate and check

The directory includes the original `source.tar.gz`, the two input templates, the source checksum manifest, and an independent Python verifier. From this directory, run the following with Bash, GNU `sha256sum`, a C++17 compiler named `g++`, and Python 3 available as `python` and `python3`. The checked run used GCC 14.2.0 and Python 3.12.14. Exact search order uses the GNU C++ standard library’s shuffle implementation.

```bash
mkdir -p source
tar -xzf source.tar.gz -C source
(cd source && sha256sum -c ../sources.sha256)
W313_LEAN_ROOT="$PWD/regeneration-support" \
  bash source/reproduce.sh "$PWD/regenerated"
(cd regenerated && sha256sum -c ../sources.sha256)
python3 verify_tapes.py regenerated
```

`verify_tapes.py` accepts any directory containing the width-159 `dag.json` and the corresponding Lean sources. It can also check the original archive sources using `python3 verify_tapes.py source`. It uses sets to verify the state transitions independently of the C++ search and the Lean evaluator.

The regenerated 70 Lean module sources and `dag.json` matched the originals byte for byte. The search returned `sat=0` after 147,542 calls, with search depth 42 and 14 dependency levels. The independent checker verified every operation in 927 fragments, with 20,197 empty progressions, 107,149 forced red positions, 20,196 exhaustive splits, and 926 links to already verified states. The maximum depth within a fragment was 32. It also verified the root seed and its allowed positions.

| Input | SHA-256 |
| --- | --- |
| `source.tar.gz` | `bd32dbb46d5ee49c9558c0d64ebbcdaf6530a621599c34552afda7d3f05288bb` |
| `sources.sha256` | `20f9aa6c07f779ef222239860678fb6ef6251d0bc2df04d7f5ae5733ef3dc383` |
| `source/H3AfterGapSevenEndpoint.lean` | `250e0d3cc0e3c23dbf00dccfe51c700890f0573545ce1390d1a7c9c2ed8b4b22` |

## Replay in Lean

Use Lean 4.33.1 at commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. The final window needs the previously compiled `Green160NearWitness` module. The exact H3 bridge also needs the previously compiled `H3AfterGapFiveInterior` module. Supply the directories containing these modules and their transitive dependency outputs in `LEAN_PATH`. The arithmetic shards use the Lean standard library and this certificate’s preceding shards. The original `finish.sh` in the archive records the local cache layout used in the first replay.

Set `LEAN` to the matching Lean executable and `LEAN_PATH` to those dependency paths before running the following from this package directory. The commands compile the original sources with one worker, set a configurable memory ceiling, and put each module’s diagnostics in its own log. Choose `LEAN_MEMORY_MB` for the available memory, especially for the final imports. The local 2,048-MiB setting passed the next arithmetic shard.

```bash
set -euo pipefail
cd source
export LEAN_PATH="$PWD${LEAN_PATH:+:$LEAN_PATH}"
"$LEAN" --version
lean_memory_mb=${LEAN_MEMORY_MB:-2048}
python3 -c 'import json; print(*json.load(open("dag.json")), sep="\n")' |
  while IFS= read -r module; do
    "$LEAN" -j1 "-M$lean_memory_mb" -o "$module.olean" "$module.lean" > "$module.log" 2>&1
    printf 'Checked %s\n' "$module"
  done
"$LEAN" -j1 "-M$lean_memory_mb" -o H3AfterGapSevenEndpoint.olean H3AfterGapSevenEndpoint.lean \
  > H3AfterGapSevenEndpoint.log 2>&1
python3 audit-axioms.py
```

The local original replay left two durable compiled modules in DAG order: `Green159GapSevenCore` and `Green159GapSeven0D001Part0`. Together they contain 44 of 927 certificate fragments. A later single-shard replay compiled `Green159GapSeven0D001Part1` with `-j1 -M2048` in 17.357 seconds after a 1,500-MiB run hit the kernel memory ceiling. The final durable prefix contains 46 original modules and 827 of 927 certificate fragments, through `Green159GapSeven0D013Part2`. `durable-prefix.sha256` records the local compiled output hashes in DAG order. The next original module is `Green159GapSeven0D013`. The unconditional bridge and axiom audit remain pending.

A later grouped run eliminated repeated imports and reached `Green159GapSeven0D004Part0`, the 14th original source block, with 341 fragments reached including the then-durable two-module prefix. The worker exited with status 137 after 1,024.69 seconds wall time. Its last sample recorded 767,198 major page faults and 1,693,748 KiB RSS. It produced no grouped `.olean`; the final bridge stage and unconditional axiom audit remain pending. The archive’s existing `ConditionalBridge.log` is for a bridge with the shifted-window result as a hypothesis.
