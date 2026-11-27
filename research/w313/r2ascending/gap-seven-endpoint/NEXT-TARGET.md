# W(3,13) R2.H3 gap-seven endpoint

The next candidate is the normalized alternating tuple `(0,7,0,7)`. A width-159 window anchored at 0 uses the red seed `[0,2,92,94]` and search order 8. If the certificate and bridge pass, literal H3 reduces to 16 alternating and 4,882 nonalternating tuples.

## Reproduction

Run `./reproduce.sh` to regenerate 70 Lean modules and `dag.json` in a printed temporary directory. Give the script an output directory to choose where it writes. The script compiles the included C++ search source and splits the resulting proof into bounded shards. Generation took 1.465 seconds wall time. The search emitted 927 fragments from 147,542 nodes, with depth 42 and 14 dependency levels.

Run `./finish.sh` in the package directory to check the included DAG and the exact H3 bridge with pinned Lean 4.33.1. It uses the existing W(3,13) replay outputs at the paths set in that script and checks one shard at a time. The 70-module replay is expected to take about 8–10 minutes based on the measured 6:10 replay of the 51-module gap-five height-one certificate.

The planned theorem is `OMA.GreenR2GapSevenEndpoint.h3_iff_remaining_alternating_and_nonalternating` in `H3AfterGapSevenEndpoint.lean`. The bridge typechecks under the exact shifted-window hypothesis in `ConditionalBridge.lean`. The unconditional certificate replay is pending.
