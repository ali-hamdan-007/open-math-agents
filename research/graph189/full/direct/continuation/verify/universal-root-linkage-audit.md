# Universal-root linkage in the complement of a longest path

Let \(H=G-w\), let \(P\) be a longest path of \(H\), and let \(x\) be a high vertex in a nontrivial exterior component. Write \(q=|N_H(x)\setminus P|\) and \(X=\{x\}\cup(N_H(x)\setminus P)\). Every \(y\in X\setminus\{x\}\) is adjacent to \(x\), and
\[
d_{H[X]}(y)=1+|(N_H(y)\setminus P)\cap N_H(x)|.
\]
The sharp exterior-contact inequality bounds \(a_x+d_H(y)\) by \(k+d_{H[X]}(y)\), where \(a_x=d_H(x)-q\). Since \(x\) is high, \(d_H(x)\ge k-1\). Thus \(d_{H[X]}(y)\ge k-q-2\) for high \(y\), and \(d_{H[X]}(y)\ge\delta-q-2\) for every \(y\).

Assume \(s\ge5\), \(k\ge26\), \(k\ge3s+1\), \(2\delta\ge k+2s+2\), and \(s+1\le q\le2s-1\). The high bound is at least \(s\). The uniform bound is at least \(\lceil k/2\rceil-s\ge5\). For \(s\le8\) this follows from \(k\ge26\), and for \(s\ge9\) it follows from \(k\ge3s+1\). The center has degree \(q\ge s+1\).

For distinct requested endpoints \(a,b\ne x\), take a longest path rooted at \(a\) in \(X\setminus\{x,b\}\). If it ends at the exceptional low vertex, the latter has at least two neighbors in this induced graph. Each is already on the path by maximality. Pivot on any neighbor other than its immediate predecessor and reverse the suffix. This preserves \(a\) and makes the new free end a high vertex. A pivot at \(a\) is allowed. Every neighbor of this high end is already on the path, so it has at least \(s-1\) vertices. Appending \(x,b\) gives at least \(s+1\). When one endpoint is \(x\), root at the other endpoint and delete only \(x\). The same argument yields at least \(s\) vertices before appending \(x\). The entire construction stays in \(X\), which has \(q+1\ge s+2\) vertices. If one of the removed vertices or the anchor is exceptional, the free-end bound still holds.

In the other branch every high exterior vertex in the component has exterior degree at least \(2s\). Delete the possible low vertex. The surviving graph has minimum degree at least \(2s-1\). A longest path gives a cycle on at least \(2s\) vertices by joining its endpoint to its farthest neighbor. The longer arc between any distinct prescribed pair on the cycle has at least \(s+1\) vertices. Both branches therefore furnish the vertex-counted linkage at parameter \(s+1\) of the upstream linked-set theorem.
