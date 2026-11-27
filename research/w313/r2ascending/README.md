# Two normalized ascending R2-H3 fibers of W(3,13)

The ascending adjacent ray heights $(h,h+1,h,h+1)$ meet R2-H3's two sign tests and normalization exactly for $0 ≤ h ≤ 5$. Their red points in increasing order are $13h$, $13h+2$, $13h+14$, and $13h+16$.

The checked width-147 window fixes red points 52, 54, 66, and 68. The 160-point translation offsets 0 through 13 give starts 52 through 65. Reflection gives starts 78 through 91, for 28 distinct exclusions of the four-red shape $(a,a+2,a+14,a+16)$. Its normalized ray fits are $h=4$ and $h=5$, and their unnormalized reflections are $h=7$ and $h=6$ respectively.

The theorem `OMA.GreenR2Ascending.r2_h3_ascending_heights` proves these four raw fibers under the exact R2 no-red-triple, shorter-step hitting, and ray-red assumptions. Four normalized ascending adjacent fibers and the rest of H3 remain outside this certificate.

The search for the retained window used 33,857 nodes and emitted 222 proof fragments. The two window source files use 196,295 bytes in total. The bounded pilot found no single checked candidate covering three normalized heights among its sampled windows. At start 52, the solver found progression-free extensions at widths 143 and 144 and closed the branch at widths 145, 146, and 147. Width 147 used the fewest nodes of the three closing runs.

## Check and regenerate

From `parallel/ramsey`, with `Green160NearWitness.olean` in the existing focused dependency tree:

```sh
g++ -std=c++17 -O3 search160.cpp -o search160
python3 r2ascending/make_window.py 52 --width 147 --shape 0,2,14,16
for module in Green147WindowCore Green147Window52 GreenR2Premises; do
    ./lean-focus.sh -o "focused/$module.olean" "r2ascending/$module.lean"
done
./lean-focus.sh r2ascending/GreenR2Ascending.lean
```

The modular bundle uses Lean 4.33.1. It needs the shared `Green160NearWitness.lean` and the listed files only. The descending proof modules are independent of this certificate. The search pilot can be rerun with `python3 r2ascending/probe.py`.

The text-only publication bundle preserves `Green160NearWitness.lean` and the `r2ascending` directory. Run `r2ascending/verify.sh` with Lean 4.33.1 to build the modules sequentially in a temporary directory, or set `LEAN_BIN` to the executable. The saved audit logs record the focused build for every theorem.
