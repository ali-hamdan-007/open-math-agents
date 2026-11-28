# One separator certificate for both high-order bounds

The terminal separator argument, when fully joined, excludes a counterexample in **any** valid band at its own parameters. Only the four fields s,k,low,cap enter this implication. Consequently the two asymptotic upper-order assumptions of the scalar reduction can also be removed by constructing valid bands. There is no need for two separate copies of the global separator argument.

Write R=n−s−1−(s+1)k. Take s≥5, k>6(s−1), R≥s and (s−1)R≥2k. Choose z=⌊k/(s−1)⌋, set the population cap m=k+z, and set both band endpoints to n. This row passes the complete predicate valid from Graph189FiniteDomain.lean.

Indeed 2z≤R, z<R and z≤k/2. With h=n−s−1, a=m+1 and b=h−k−a, we get b≥(s−1)k. The floor gives (s−1)(z+1)>k, so ab>sk². Also b≥(s−1)k and b−k≥2k give b(b−k)>sk². The small-side cap m<2k−s follows from k>2s and z≤k/2. The order test and strict large population test follow from R≥s and R>z.

The integer private-support test needs (s+1)z+k+s−s²(s−1)<sR. Since (s−1)z≤k, 2z≤R and 2k≤(s−1)R, already (s+1)z+k≤sR. The leftover term is strictly negative. For c=1,2 put d=s−c≥3. Then dR≥k since 2(s−2)≥s−1. The additional debit d(d−1)−c−1 is positive, which gives the strict residual-singleton test. These are all the validity conditions.

In particular either 2n≥(2s+3)k+4s+4 or (s−2)(n−2s−3)≥((s+1)(s−2)+3)k gives both conditions on R. In the first case 2R≥k+2s+2. In the second case (s−2)(R−s−2)≥3k. Thus the geometric implication for valid bands supplies both high-order assumptions throughout the unbounded range. This argument leaves the lower order coming from a long cycle and its critical-connectivity lift as independent inputs.
