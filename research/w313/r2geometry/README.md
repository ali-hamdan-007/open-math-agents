# R2 fibers from the checked four-red windows

The width-154, 150, 137 and 130 certificates all use the offsets $(0,2,12,14)$. The Lean theorem `forces_of_covered` gives a single 160-point implication for any start in
$[1,7] ∪ [14,24] ∪ [27,118] ∪ [121,131] ∪ [138,144]$.
There are 128 such starts. The two width-141 seeds and the prior 160-point seed use offsets $(0,4,5,32)$. Including both shapes yields 210 distinct four-red exclusions under shifts and reflection. All windows have width at least 130, so an AP-preserving affine embedding into 160 points has step one up to reflection.

The R2 rays have residues 0, 1, 2 and 3 modulo 13. If the symmetric shape fits the four rays, its first two points force $a$ modulo 13 to be at most 1, and its third rules out residue 0. Thus $a=13h+1$. The four heights must then be $(h+1,h,h+1,h)$ with $0 ≤ h ≤ 11$. Every corresponding start is in the certified ranges. Exactly $h=0,1,…,5$ satisfy H2's normalization. The other six are their reflections.

The earlier shape has required points $a,a+4$. They cannot both lie on the four rays since their difference is 4. Reflection swaps the rays while preserving this impossibility. For an alternating pair of heights $(i,j,i,j)$, reflection sends it to $(12-j,12-i,12-j,12-i)$, preserving its direction. Ascending alternation has point offsets $(0,2,14,16)$ and is outside this certificate family.

`r2_of_covered_shape` applies the generic four-red theorem directly to the R2 hypotheses. It uses the given shorter-step hitting predicate for every 13-progression of step at most 12. The four ray witnesses supply the step-13 cases. It accepts arbitrary R2 heights and a certified inclusion of the four seed points in the ray set.

## Check

From `parallel/ramsey`, with the completed adjacent-family modules already built:

```sh
./lean-focus.sh r2geometry/GreenR2SeedGeometry.lean
python3 r2geometry/classify.py
```

The classifier enumerates only the affine images of the checked seeds. It checks exactly 12 raw ray fits, six normalized H2 fits, and zero normalized H1 or H3 fits. Lean independently verifies the shape and reflection arguments. No additional proof search or tape files are required.
