# A disconnected or cut nontriple layer in the one-extra triangle

Use the setup and bounds of single-extra-hamilton.md, with \(k\ge9\), but now suppose that the nontriple layer \(F\) is disconnected or has a cut vertex. The original graph has a Hamilton path in both cases.

Let \(Z=\varnothing\) if \(F\) is disconnected and let \(Z=\{r\}\) if \(r\) is a cut vertex of the connected graph \(F\). Consider the components of \(F-Z\).

## Each relevant support stays in one component

The closed full remote support neighborhoods satisfy \(|H_I|\le2k-7\) for all \(I\in\{P,Q,J,D\}\). For \(D\), use \(|H_D|\le (k-5)+a_D+2\) and \(a_D\le k-4\). For \(P,Q\), use \(|H_I|\le (k-2)+a_I+1\) when \(a_I\le k-6\). Otherwise \(I\) sees all but at most one common middle, while the other one of \(P,Q\) sees at least two, so they have a paired common occurrence. Then \(|S_I|\le k-6\), giving \(|H_I|\le(k-5)+(k-4)+1=2k-8\). For \(J\), use \(|H_J|\le (k-3)+a_J+1\) if \(a_J\le k-5\). Otherwise \(J\) sees every common middle and pairs with \(P\), yielding the same stronger bound from \(|S_J|\le k-6\).

If a support meets two components, the remote closed neighborhoods of its two chosen nontriple supporters have order at least \(k-2\) each. Their intersection is contained in \(Z\cup\{t\}\). Their union lies in that support's \(H_I\) and has order at least \(2(k-2)-2=2k-6\), a contradiction. Thus each supporting middle occurs in at most one component.

Every component needs at least two supporting middles. If it had just one, each component vertex would have only that middle, at most one removed nontriple \(r\), and \(t\) available as outside neighbors, forcing component order at least \(k-2\). But a true private has at most \(k-3\) nontriple supporters and \(D\) at most \(k-6\). Hence there are exactly two components \(X,Y\), each using exactly two supporting middles. As all but \(D\) have true solos, the components contain solos. Each component therefore has order at least \(k-2\) in the cut case and at least \(k-1\) in the disconnected case, and minimum degree at least \(k-4\) in the cut case or \(k-3\) in the disconnected case. Indeed other than their at most two supporting middles, component vertices can only neighbor \(t\) and possibly \(r\). The global order bound \(m\le\lfloor(5k-13)/2\rfloor\) now gives
\[
 \max\{|X|,|Y|\}\le\lfloor(3k-11)/2\rfloor
\]
in either case, subtracting the other component and possibly \(r\).

## Spanning component paths

In a component with two true supporting middles, use solo remotes as candidate endpoints for their respective supports. Each has at least one candidate, and at least one class has at least two, since \(P,Q\) each start with three solos and deleting \(r\) removes at most one. In the component with \(D\), take any \(D\)-supporter as its candidate, and choose the other endpoint from true solos. There are at least four true solos there: the order is at least \(k-2\), \(|S_D|\le k-6\), and every vertex not supported by \(D\) is a solo of the component's true private.

If \(t\) has a common middle neighbor, reserve it for the end of the final path. Otherwise assign \(t\) to a component where it has two neighbors for insertion in a spanning path. Such a component exists: as in single-extra-hamilton.md, \(d_F(t)\ge k-3\), so there are at least \(k-4\ge5\) neighbors among the two components even after deleting \(r\). Also assign \(r\), if present, to a component with at least two neighbors, using \(d_F(r)\ge k-4\ge5\).

If both \(r,t\) need assignment, put them in distinct eligible components when possible. Otherwise they have the same unique eligible component, and each has at least \(k-5\ge4\) neighbors there because the other component contains at most one neighbor of each. Choose disjoint pairs of neighbors for those two insertions. In the other component at most two solos can touch \(r\) or \(t\), and there are at least three solos there. Thus a solo avoids both; its only possible external neighbor is its unique support and its degree forces that component to have order at least \(k\). In this case the component receiving both insertions has order at most \(\lfloor(3k-15)/2\rfloor\).

In each component the assigned neighbor pairs form a matching on the underlying component. Choose the two component path endpoints from the candidate pools above so they lie in distinct matching blocks (count unmatched vertices as one-vertex blocks). The pools are disjoint and one has at least two candidates; first choose from the smaller pool, whose block can consume at most one candidate from the larger pool.

Add to the component an endpoint marker adjacent only to the chosen endpoints. Also include each vertex assigned for insertion, with just its two reserved neighbors. In the cut case the underlying component degree sum on any pair is at least \(2(k-4)\). This is at least the augmented graph order with at most one insertion, since \(\lfloor(3k-11)/2\rfloor+2\le2(k-4)\) for \(k\ge9\). If it receives two insertions, use \(\lfloor(3k-15)/2\rfloor+3\le2(k-4)\). The degree sum in the disconnected case is at least \(2(k-3)\) and the order bound with at most one insertion again suffices. Thus Bondy–Chvátal closure permits adding every missing edge within the underlying component.

In that completed clique, order the matching blocks with the chosen endpoint blocks first and last, and orient those blocks with the chosen endpoints at the outside ends. Subdivide prescribed matching edges by their assigned vertices and close the resulting path through the endpoint marker. Closure transfers the Hamilton cycle to the original augmented graph, and removing the marker gives the desired component path with prescribed supported endpoints and assigned insertions.

## Join the paths through the middle and anchor layers

If the two component support types are \(P,Q\) and \(D,J\), label them \(X,Y\) respectively and concatenate
\[
 P,\ X,\ Q,\ B,\ D,\ Y,\ J,\ C,\ z,\ A,\ W.
\]
If their types are \(P,D\) and \(J,Q\), label them \(X,Y\) and concatenate
\[
 P,\ X,\ D,\ A,\ z,\ C,\ J,\ Y,\ Q,\ B,\ W.
\]
The case where \(D\) pairs with \(Q\) follows by interchanging \(P,Q\) and \(A,B\). An occurrence of \(X\) or \(Y\) stands for its component path with the appropriate orientation. The anchor preceding \(W\) touches every common middle. The common middles miss at most one another, and \(|W|\ge5\), so \(W\) has a Hamilton cycle by Dirac. Traverse that cycle as a path ending at a neighbor of \(t\) and append \(t\) if it was reserved. Otherwise follow the cycle as a path starting anywhere. In each case the resulting path spans.
