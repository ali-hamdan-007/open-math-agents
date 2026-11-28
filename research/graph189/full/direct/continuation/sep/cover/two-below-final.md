# Traceability at connectivity two below half the second-smallest degree

For every k and connectivity s=floor(k/2)−2 for which this is a positive integer, every qualifying Graph 189 graph is traceable. Degrees up to eleven follow from the earlier complete small-degree results, and degree thirteen is covered in ../../verify/k13/traceability.md. For the other parameters we establish that the optimized smallest high-bearing exterior component C is 2-connected of order m≤2q−1, with q the least C-degree of its high vertices. This is impossible: its maximum C-to-P matching j≥s satisfies 3j≥k, contrary to local-cover-contacts.md.

For even k=2t≥12, the exterior reduction itself was proved for every t≥6 in ../k12/even-two-below.md. This gives a solver-free proof of the remaining degree-twelve case as well.

For odd k=2t+1 with t≥7, put h=t+1 and U=t²+6t+4. The large 2-connected case m≥2q is excluded by the argument for H=N_C[x] in ../k12/odd-two-below.md. Its matching and degree-sum inequalities hold for every t≥7: 2(q−2)≥q+2 at q=t+1. The large endblock bound, whenever q≥t+2, already exceeds U. At q=t+1, an endblock B of order b≥2q−1 has at most two ambient distance-two vertices in C from a minimizing high noncut x. A single gateway is impossible by 2-connectivity of B, so that layer R has size two, and the possible low is on P. The same H is Hamilton-connected, has order q+1 and has a matching of j=s+1 contacts to P. In B there exists a vertex outside H∪R because b≥2q−1>q+3. For any matched terminal v, B−v is connected. A path there from H−v to the outside, trimmed between its last H vertex and first outside vertex, has an intermediary in R. Each tail traversal can therefore gain at least two vertices beyond consuming all H. The whole component has order m≥b+h≥3q−1, so

    n ≥ 3q−1 + (s+2)(q+1) + (s+1) + 4
      = (s+5)q+2s+6 = t²+6t+5 > U.

The small-endblock lower bound is t²+7t−3≥U for all t≥7. Equality only at n=U gives no low vertex. Each of the two tails then gains another vertex in the high remainder, as in the even paper, ruling out equality as well. This eliminates all cut or large alternatives in C. The stated local-cover contradiction now proves the entire connectivity line.
