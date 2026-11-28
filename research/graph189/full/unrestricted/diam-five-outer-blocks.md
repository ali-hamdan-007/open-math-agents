# Both outer blocks of a diameter-five qualifying graph are Hamilton-connected

Retain the prior diameter-five notation. Let U be induced on {z}∪A∪B, let V be induced on D+∪F, put d0=|D−D+|≤j and t=|D+|=d−d0. These are disjoint induced graphs. Each admits a spanning path between any two prescribed distinct vertices.

For U, add a degree-two marker at the two prescribed vertices and apply Hamilton-cycle closure only to original pairs. The threshold is |U|+1=a+b+2=s+i+2. Each anchor has its full degree at least s in U. A B vertex loses at most h−m middle neighbors, so retains degree at least s−h+m=f+m, and f=i+1+j+g+l≥i+2. Since s≥i+2, all missing A–A and A–B pairs meet the threshold. In the resulting graph every B vertex sees all a anchors. If a≥b+2, twice this degree already reaches a+b+2. If a≤b+1, substitute a=i+h+1+j+g and b=i+l to get l≥h+j+g, whence

    2(f+m)−(s+i+2) = l−h+j+g+2m−1 ≥ 0.

Thus B–B pairs also close. The original A∪B is now a clique, and every missing z–B pair closes because its sum of degrees is at least a+(a+b−1)≥a+b+2, using a≥3. The original vertices form a clique and hence admit a Hamilton cycle through the prescribed marker. Reverse closure and delete the marker to give the prescribed path.

For V, add its prescribed marker; the threshold is |V|+1=t+f+1=s+2+j−d0. Every far vertex has its full degree at least s. Every D+ vertex loses at most l middle neighbors and at most d0 neighbors in D−D+, so retains degree at least a−d0. Since a≥j+2, the F–F and F–D+ pairs close. If f≥t+1, twice the new degree of every D+ vertex is at least 2f≥t+f+1. If f≤t, substituting f=i+1+j+g+l and t=h+1+j−d0 gives i+g+l+d0≤h, so

    2(a−d0)−(s+2+j−d0) = i+h−l+g−d0−1 ≥ 2i+2g−1 ≥ 1.

In both cases all remaining original pairs close, and the same reversal gives the prescribed Hamilton path in V.

Consequently, with T induced on C∪(D−D+), any spanning path of T whose distinct endpoints respectively touch U and V yields a spanning path of G: prepend a U spanning path ending at the matched U vertex and append a V spanning path beginning at the matched V vertex. More generally, either outer block can be inserted anywhere between two distinct remaining vertices having distinct contacts in that block, using an appropriate prescribed spanning path. In particular a three-path cover of T suffices if the two needed joins admit distinct contacts in U and in V, respectively. These facts are valid at all orders and do not require a triangle-free hypothesis.
