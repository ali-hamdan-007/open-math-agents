# A finite certificate for the moderate case at degrees 3, 4, 5 and 6

Let G be a two-connected counterexample in the moderate range 2k+3≤n≤3k+2. Put h=ceil(k/2) and delete a minimum-degree vertex z. Every remaining vertex is high in G and has degree at least k−1 in the connected graph H=G−z. Choose a longest H-path P of order p, and write b for the number of H vertices outside P. All graph distances in the hypothesis below are measured in G.

The preceding minimum-degree-two result disposes of δ≤2. For δ≥3 the original even- and odd-degree exterior results and the almost-spanning lemma give the global path gap, hence b≥h+1. These results precede this computation; see also [the independent scope audit](../verify/moderate-completion-audit.md). Also p≥2k−1. Indeed both path endpoints have all their H-neighbors on P. If their degree sum exceeded p−1 there would be two complementary end attachments wrapping the path into a cycle on its complete vertex set. Since H is connected and b>0, a path entering this cycle from outside would be longer than P. This standard longest-path argument is also the content of the registered R2's lemma4. Since n=p+b+1 we have b≤k+2. The finite calculation therefore needs at most eight exterior vertices.

**Exterior types and contacts.** Generate every simple graph E of order b up to isomorphism, including disconnected graphs. The Python generator extends each graph of order b−1 with each possible neighborhood of one new vertex, and identifies isomorphic results by minimizing a graph encoding over orderings within isomorphism-invariant color classes. Vertices whose transpositions preserve the adjacency matrix need only be ordered once. The counts from orders one through eight are 1, 2, 4, 11, 34, 156, 1044 and 12346. Let d(x) count neighbors of x in E. At most one vertex may be isolated by the shifted-contact saturation argument, and every nonisolated x has d(x)≥h−1, as in [the degree-nine proof](moderate-degree-nine.md).

For each exterior vertex x enumerate its complete set A(x) of contacts on P. Then |A(x)|+d(x)≥k−1. For an isolated exterior vertex |A(x)|=k−1. For an exterior edge xy the exact cross-contact inequality is

    |A(x)| + |A(y)| + d(y) ≤ k+d(x).

In particular |A(x)|≤d(x)+1 when x is nonisolated. Consecutive contacts of x would permit insertion. Any P contact of x has at least L(x) unmarked positions in either direction, where L(x) is the longest order of an exterior path starting at x. Between distinct contact indices of x and y there are at least L(x,y) interior positions, where L(x,y) is the longest order of a simple path in E from x to y (zero when disconnected). These follow by replacing an outer tail or an inner interval of the longest H-path. Every component of E needs at least one contact.

Whenever |A(x)|+d(x)=k−1 we must have x adjacent to z in G. An exterior vertex has at most k positive even-distance witnesses. Count the forced nonneighbors of x connected by guaranteed two-edge walks, both on P and in E. These conditions use only necessary properties and apply to every completion. The remaining attachment counts are tabulated below.

**Testing completions.** For each attachment pattern the mandatory graph L contains all path edges, the exact exterior graph, all actual exterior-to-path contacts and the forced z-edges. Its possible supergraph U can add only chords of P and further edges at z. If L contains a path of order n−h−1 in G or a path of order p+1 in H, the pattern is impossible. Any optional edge that would already produce one of these contradictions when added to L must be absent. Remove it from U. If U lacks two-connectivity, a required vertex degree, or permits too few adjacencies to prevent k+1 forced distance-two witnesses, no completion works. Finally, if a vertex has exactly the required number of possible neighbors, all those neighbors are mandatory. Repeat until an exclusion or a fixed point. There is no branching on optional edges.

| k | Attachment patterns | Excluded by a path in the mandatory graph at the first test | Excluded by monotone completion constraints | Survive |
|---:|---:|---:|---:|---:|
| 3 | 9 | 8 | 1 | 0 |
| 4 | 30 | 7 | 23 | 0 |
| 5 | 51 | 7 | 44 | 0 |
| 6 | 98 | 4 | 94 | 0 |

Reproduce the primary computation with Python 3.10 or newer:

```sh
python3 root/moderate_exterior_search.py 3 4 5 6 --complete
```

The independent implementation builds its own unlabeled graph representatives, computes longest paths separately and applies completion propagation. Both produce the table above. Compile and run it from the continuation directory:

```sh
c++ -std=c++17 -O2 verify/moderate-completion-independent.cpp -o /tmp/moderate-independent
/tmp/moderate-independent
```

Combined with the focused k≤2 theorem and the degree-seven-and-above routing argument, this gives a separate computer-assisted paper proof of **all of the moderate parent case**. The finite graph calculations were run in Python and C++. Translating the graph-to-enumeration reduction and its finite certificates into Lean is outstanding. The separate large-order parent case and the official verdict for the exact parent are still outstanding.
