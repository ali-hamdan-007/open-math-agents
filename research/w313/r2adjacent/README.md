# The adjacent alternating-height family in W(3,13) R2-H2

The normalized heights $(h+1,h,h+1,h)$ belong to R2-H2 exactly for integers $0 ≤ h ≤ 5$. The two second differences are $2$ and $−2$, and both sums used for normalization are $2h+1$. The corresponding red points, in increasing order, are
$13h+1$, $13h+3$, $13h+13$, and $13h+15$.

The first set of kernel proofs covers the subfamily $1 ≤ h ≤ 5$ under the ray, no-red-triple and shorter-step hitting assumptions of R2-H2.

| Heights | First red point | Certificate | Search nodes | Tape fragments |
| --- | ---: | --- | ---: | ---: |
| $h=1$ | 14 | Width 150, local start 14 | 27,178 | 187 |
| $h=2,3$ | 27, 40 | Width 137, local start 27, shifted by 0 or 13 | 6,616 | 52 |
| $h=4,5$ | 53, 66 | Earlier width-130 certificate in `../window141` | 2,603 | 19 |

The two new tapes use 193,678 bytes of Lean source, excluding their small checker copies and parameterized bridge. Upstream R2-H2 has 4,924 normalized tuples. The five certified tuples here include the two previously certified, so the incremental progress is three more tuples. The edge tuple isolated by this first set has $h=0$ and red positions $(1,3,13,15)$. The exploratory solver closes it on a width-154 window after 127,771 nodes and on 160 after 129,119 nodes. The separately packaged edge completion uses the width-154 run.

The wider normalized alternating family $(i,j,i,j)$, with $j<i$ and $i+j ≤ 12$, has 42 tuples. The pilot search closed 15 within 100,000 calls and reached its cap on 27. The adjacent cases in the table and the separately packaged edge case have checked certificates. The two recorded search logs use the existing 100,000-node solver cap.

## Reproduce

Run from `parallel/ramsey` with the existing Lean 4.33.1 harness and earlier `window141` dependencies:

```sh
g++ -std=c++17 -O3 search160.cpp -o search160
python3 r2adjacent/make_window.py 27 --width 137 --shape 0,2,12,14
python3 r2adjacent/make_window.py 14 --width 150 --shape 0,2,12,14
for k in Green137WindowCore Green137Window27 Green150WindowCore Green150Window14; do
    ./lean-focus.sh -o "focused/$k.olean" "r2adjacent/$k.lean"
done
./lean-focus.sh -o focused/Green130R2Bridge.olean window141/Green130R2Bridge.lean
./lean-focus.sh r2adjacent/GreenR2Adjacent.lean
```

The remaining input dependencies are the prior `Green160NearWitness.lean`, `window141/Green130WindowCore.lean` and `window141/Green130Window64.lean`. The latest build prints the axiom audits for both parameterized theorems.

The two pilot logs can be regenerated with `python3 r2adjacent/screen.py` and `python3 r2adjacent/screen.py --windows`. For the edge sensitivity check, compile a temporary solver with an 800,000-node cap:

```sh
sed 's/++calls>=100000/++calls>=800000/' search160.cpp > /tmp/r2-cap800k.cpp
g++ -std=c++17 -O3 /tmp/r2-cap800k.cpp -o /tmp/r2-cap800k
python3 r2adjacent/screen.py --edge --solver /tmp/r2-cap800k
```

The edge completion is packaged separately. See [edge154/PUBLICATION.md](edge154/PUBLICATION.md) for the six-case theorem, complete source layout, and sequential build commands.
