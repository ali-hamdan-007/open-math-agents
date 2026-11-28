# Four-connectivity at second-smallest degree at least 26

Let \(G\) satisfy the original Graph 189 hypotheses and have vertex connectivity four. Write \(k\) for its second-smallest degree and \(n\) for its order. The local Lean theorem Graph189FourCut.traceable proves the desired Hamiltonian-path conclusion at every order for \(k\ge37\). This note records the scope of the complementary finite argument for \(26\le k\le36\).

Suppose \(G\) is not traceable. A Hamiltonian deletion of a minimum vertex is impossible by Graph189RootedSplice.traceable_of_hamiltonian_minimum_deletion. The linked-set cycle bound at parameter four in the completion at a minimum vertex gives \(n\ge5k-11\). The upper-order theorem Graph189FourCut.exclude applies at \(n\ge6k-10\), so \(n\le6k-11\).

If a low vertex \(z\) lies on any minimum cut, the audited separator bound in four-connectivity-assembly.md gives \(n\le5k-2\). The ordinary opposite-neighbor wedge and the lower bound \(5k-11\) give \(f=\deg(z)=k-1\). The critical-connectivity theorem supplies a universal completion of connectivity five, whose minimum degree is at least \(f\). The already checked critical linked exterior at parameter six gives a linked exterior at five, and the order estimate at minimum degree \(f\) gives \(n\ge6k-25>5k-2\). Thus every minimum separator consists entirely of high vertices. If the minimum vertex is low, its universal completion raises the connectivity to five and has minimum degree at least \(k\). The parameter-five linked exterior in this completion gives \(n\ge6k-19\). If the minimum degree equals \(k\), the critical completion also raises the connectivity to five and preserves the minimum degree lower bound \(k\), giving the same order. In the finite range, every possible counterexample therefore satisfies

\[
6k-19\le n\le6k-11.
\]

Take any partition of the remaining vertices into nonempty sides of a minimum cut, oriented with the smaller high population \(x\) first and the larger \(y\) second. The sum \(x+y\) is \(n-4\) or \(n-5\). The ordinary cross-product bound gives \(xy\le kx+4k^2\). At any row satisfying the existing strict four-cut numerical inequalities, the smaller side must have at least two labels shared by all its high vertices.

For \(26\le k\le30\), the strict support covers in four-cut-degree30.md and the slack argument in four-cut-one-common.md extend the geometric conclusion to any row with \(y\ge4k-1\) and \(4(4k-11+x)+x<4(x+y)\). Indeed the private-port branch is excluded by the last inequality, the one-common branch by the slack argument, and the co-singleton branch by the twofold cover. For \(y=4k-1\) or \(4k\), we have \(x\ge2k-24>k\), which precludes even one common label. The strengthened covers close this equality and near-equality range. For \(y>4k\), the high-label and support classification lemmas used in the original proof apply directly. The order inequality \(n>5k+5\) follows from \(n\ge6k-19\) and \(k\ge26\).

The remaining rows have independent conditions. At degrees 34 through 36 the strict cross-product inequality removes them all. At degrees 32 and 33 the audits in four-cut-strict-product.md remove the explicit exceptions. The record four-cut-degree31.md gives the nine initial rows and their proof, with a separate exact mask relaxation for the hardest row. The degree-30 note eliminates its five rows by separator counts. Degree 29 has the nine population rows and seven distinct profile pairs in four-cut-degree29.md. At degrees 26 through 28 the reproduced table begins with 43, 29 and 18 population rows after the same verified and paper inequalities. All these rows have \(x,y>k\), so the nonempty nearest-label profile for high nonports applies. The masks, row filters, positive controls and solver log are in the accompanying replay files. Every mask row uses all four anchors high from the earlier exclusion. Degree 29 additionally uses the explicit bounds on the direct contact counts proved in its note.

Once the finite rows are excluded, every oriented minimum cut has \(y>4k\) and two labels common to the smaller side's high vertices. The final existing recut argument can therefore be applied at the original separator and at the separator it constructs. A full small-side high port gives a suitable high private large-side port by Graph189FullLabelExit.full_exit. If there is no full high port, exactly two labels are common, because every label has a high contact. The checked residual-private inequality forces a high private large-side port at one of those common labels. In the absence of such a contact it would give \(2y\le6k+x+6\le7k+6<8k\). The missing-label degree count makes that port's recut admissible. The recut has a side of size at most \(2k\) by the two-root cover, and this side contains the high private port whose support remains private in the new separator. Reorienting the new minimum cut puts this side first, since \(n\ge6k-19>4k+4\). Its high private port contradicts the two common labels.

The all-order result at \(k\ge37\), the exact-column cross-product inequality and the Hamiltonian minimum-deletion branch have local Lean verification. The graph-to-mask argument and the finite exact Z3 exclusions give a computational argument for the additional degree range. A kernel certificate for the finite profile elimination and its integration into the parent theorem are separate tasks.

## Reproducing the finite calculation

Run the commands from this directory in an active Graph 189 research checkout. If the lease-state directory is separate, point GRAPH189_LEASE_DIR to the existing directory monitored by the lease owner. The solver wrapper loads libz3.so.4 through ctypes. Each row subprocess stops when the lease state changes.

    python3 four_cut_strict_product.py
    python3 check_degree29_masks.py
    python3 check_degree26_28_masks.py

The third script can resume with --resume followed by a previous solver log. The original and resumed logs record separate segments of the same calculation.
