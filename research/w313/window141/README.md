# Transportable upper-bound branches for W(3,13)

In 0-based indexing, a window of length 141 with its four color-0 points at $(a, a+4, a+5, a+32)$ contains either a color-0 progression of length 3 or a color-1 progression of length 13 when $a=43$ or $a=73$. Embedding the window in a 160-point interval gives 20 translations per seed. Reflection gives 20 more per seed. Two tapes certify 80 distinct four-red exclusion clauses.

A window of length 130 has the same conclusion for the four color-0 points $(64, 66, 76, 78)$. Translation and reflection give the red sets $(a, a+2, a+12, a+14)$ for every $51 ≤ a ≤ 94$ on 160 points. This yields another 44 distinct clauses. Two of them directly close normalized R2-H2 tuples with heights $(5, 4, 5, 4)$ and $(6, 5, 6, 5)$. The Lean bridge proves these under the same no-red-triple, shorter-step 13-progression hitting, and ray-red premises as R2. These results cover specific branches of the 160-point upper bound.

The prior file `../extension160/Green160FourRed.lean` adds two more certified clauses, for 126 total. The checker uses kernel evaluation (`decide +kernel`) of the generated tapes. The width-141 seeds use 136 and 134 tapes and the width-130 seed uses 19. All translated, reflected and R2-fiber theorems audit to `propext`, `Classical.choice` and `Quot.sound`.

## Exact coverage on all two-colorings

| Families | Clauses | Coverage |
| --- | ---: | ---: |
| All width-141 seed-73 translations and reflections | 40 | 86.349246317223% |
| All width-130 translations and reflections | 44 | 86.693495677577% |
| Seed 73, first ten seed-43 offsets and their reflections, starts 51–63 of width 130, and both prior clauses | 75 | 96.189714595701% |

The last percentage is the exact fraction $4651449182244186746524851/4835703278458516698824704$, and a lower bound on the total family coverage. These percentages refer to uniform unrestricted two-colorings.

## Reproduce

From the parent directory that contains `search160.cpp`, regenerate the checked source if desired:

```sh
g++ -std=c++17 -O3 search160.cpp -o search160
python3 window141/make_window.py 43
python3 window141/make_window.py 73
python3 window141/make_window.py 64 --width 130 --shape 0,2,12,14
```

Use Lean 4.33.1 and build sequentially:

```sh
window141/verify.sh --old
```

Set `LEAN_BIN` if the desired Lean executable is outside `PATH`. See [PUBLICATION.md](PUBLICATION.md) for the complete modular bundle. A combined proof file exceeded the local build memory limit.

Export DIMACS clauses with variables 1 through 160 and positive literals denoting red, or compute exact coverage via variable elimination:

```sh
python3 window141/coverage.py 73:20 43:20 --old --r2 51:94 --dimacs
python3 window141/coverage.py 73:20 43:10 --old --r2 51:63
python3 window141/r2_screen.py
```
