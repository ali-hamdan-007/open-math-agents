# Independent audit of the expanded `(3,3)` manuscript

Audited SHA-256: `6352e4c86b4b5159aeb788377fbdb2f478de65118ef5a5820da1455c99b24673`.
The three textual corrections were checked in revised source SHA-256
`1e350ffb7c15a189fdaa007edd4afa35102b9cf5d62fdc66177a0609f4d84ba8`.
The leaf-reversal paragraph was then inserted and checked in final source
SHA-256 `50449cad8ae59494005bc6f84b42a97214143dcb620bcd10a82b0e96895cbc9b`.

The split-core argument is mathematically sound with three mandatory
clarifications/corrections.

## Closure and the split core

Selective core closure at threshold `2k+1` has the stated terminal form:
every nonuniversal core vertex has original degree exactly `k` and was
untouched, every other core vertex is universal, and all `L-U` edges are
original.  For `|L|<=k-2`, Hall `(1,1,2)` and `|U|>=|L|+2` give the displayed
closed-graph Hamilton cycle.

Closure reversal need not preserve `pq`, but it need not do so.  The required
wording after reversal is:

* if the resulting cycle uses artificially added `pq`, shell-replace it;
* if it avoids artificial `pq`, it is a Hamilton cycle of `D`, so break a
  port-incident edge and append a shell path;
* if `pq` was original, use the same second construction.

This validates `|L|>=k-1`; lines 177--180 must use this cycle-usage case split.

For `U` nonempty, the exact calculation
`d_L(x)=l-k+2-t_x` and the common original neighbor in `U` correctly give
`t_x+|A_x|<=3`, hence the three singleton types, at most one same-anchor
double type, and internal degrees `c` and `c-1`.

## Hall contacts and `c=0,1`

Hall `(1,2,2)` can fail only at a common four-set.  After preassigning root
contact `a`, one must also exclude the other two neighborhoods alone being a
common four-set.  The same contradiction works: its remote boundary has at
least `k-6` vertices at distance two from both ports; a port with two anchors
has only two residual slots, while a sole-anchor port has total degree at
most `1+2+4=7`.  Add this observation to lines 285--288.

The `c=0` LL-versus-UU balance is correct: starting in `U` requires
`LL>=UU`, while starting in `L` permits one extra `UU`.  Empty, singleton and
large color classes provide contacts of the asserted types.  For `c=1`, the
singleton vertices form a matching and double vertices are isolated; the
three color-class cases provide the required one- or two-unit balance.

Some clique edges inside `U` may be closure-added.  Rooted reversal is valid
after adjoining a leaf at the chosen root port `p`: the augmented order is
`2k+2`, so Hamilton-path closure has threshold `2k+1`, exactly the threshold
used for the core edges.  Restrict reversal to those core edges.  The leaf
remains degree one and hence an endpoint; deleting it recovers a `p`-rooted
spanning path of the original `D`.  The same leaf argument applies to `c=2`.

## `c=2`

Breaking each cycle of the degree-one/two graph `G[L]` gives at most
`floor((k+1)/2)` paths.  Exposing a root contact and inserting two internal
ports costs at most three paths total, and `k-3` universal vertices suffice
to join them for `k>=11`.

Lines 361--382 omit the case where the root contact `a` lies in `U`.  Repair:
do not spend the root-exposure cut; the two internal ports leave at most
`r+2` cover paths.  Start `p-a`, use `a` to enter the first, and use one more
universal vertex between successive paths.  This consumes at most
`r+2<=floor((k+1)/2)+2<=k-3=|U|` vertices.  Thus `c=2` closes after adding
this subcase.

**Conclusion.**  The claims through `c>=3` hold for `k>=11` after the three
incorporated corrections and the additional leaf-reversal paragraph above.
No prescribed-edge closure theorem is needed.  **Final audit: PASS** for
source SHA-256 `50449cad8ae59494005bc6f84b42a97214143dcb620bcd10a82b0e96895cbc9b`.
