# W(3,13) ascending R2, gap-three alternating heights

The four red points for heights $(h,h+3,h,h+3)$ are $13h + \{0,2,40,42\}$. Reflection in the 160-point interval changes $h$ to $9-h$, so five normalized heights cover the full range 0 through 9. The exact step is `Green14.W_3_13.R2.H3` of [merged PR #4300](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4300).

| Width | Local start | Normalized heights | Search nodes | Fragments |
| ---: | ---: | :--- | ---: | ---: |
| 145 | 26 | 2 and 3 | 35,568 | 226 |
| 147 | 52 | 4 | 23,319 | 149 |
| 157 | 12 | 1 | 51,793 | 347 |
| 159 | 0 | 0 | 98,983 | 638 |

`GapThreeGeometry.lean` reduces the exact gap-three family under the R2 premises to these four local windows. `GapThreeVerified.lean` assembles the window certificates into `OMA.GreenR2GapThree.gap_three`. `H3Remainder.lean` combines it with the earlier gap-one and gap-two theorems. It proves an equivalence between the exact H3 conclusion and the two remaining obligations. `H3LiteralAudit.lean` checks the equivalence against the merged `H3` declaration.

| Normalized case | Tuples | Coverage |
| :--- | ---: | :--- |
| Alternating, gap one | 6 | Earlier Lean proof |
| Alternating, gap two | 6 | Earlier Lean proof |
| Alternating, gap three | 5 | This certificate |
| Alternating, gap at least four | 25 | Open obligation |
| Nonalternating | 4,882 | Open obligation |
| Total | 4,924 | |

Run `python count_h3_cases.py` to reproduce these counts.

The pinned Lean 4.33.1 replay checked all 68 DAG modules, the gap-three theorem, the combined equivalence and the literal H3 audit. The theorem audits list only `propext`, `Classical.choice` and `Quot.sound`.

`check_endpoint_window.py` checks an actual width-148 countercoloring with red at 0, 2, 40 and 42, so any narrower local window that starts at the first red point also admits an avoidance coloring. Covering both h=0 and h=1 with the same positively translated window would require width at most 147 and local start 0.

The generated sources require the original pinned Lean 4.33.1 workspace and the cached `Green145AscendingCore`, `Green160NearWitness` and `GreenR2Premises` in `parallel/ramsey/focused`. Run `./finish.sh` to check the chunks and final assembly. It works sequentially in the dependency order recorded in `dag.json`. It can resume an incomplete build. Each generated fragment uses `decide +kernel`. To check dependency-ready chunks with two workers, run `python replay-parallel.py` before `./finish.sh`.

For the combined H3 remainder, first build the gap-two sources with their `./finish.sh`. Then set `GAP_TWO_DIR` to the absolute path of that build directory and rerun this bundle's `./finish.sh` to check `H3Remainder.lean` and `H3LiteralAudit.lean`.

Regeneration uses `g++ -std=c++17 -O3 -o search-gap3 search-gap3.cpp` and `python generate_gap3.py ./search-gap3`. `probe.py` and `tune.py` document the bounded window and heuristic scans. `probe.py` uses the previous gap-two search executable.
