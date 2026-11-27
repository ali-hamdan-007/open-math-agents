# Sharp order bound for clique blow-ups of a seven-cycle

Let s₀,…,s₆ be positive integers. Replace vertex i of a seven-cycle by a clique of size sᵢ, and join consecutive cliques completely. Write k for the second-smallest vertex degree, counting multiplicity, and suppose no vertex has more than k other vertices at positive even distance. Then

    n ≤ ⌊(10k+1)/3⌋.

This is the exact maximum at every feasible k. The feasible values are k=2 and every k≥4.

**Upper bound.** Members of class i have degree sᵢ₋₁+sᵢ+sᵢ₊₁−1 and positive even-distance count sᵢ₋₂+sᵢ₊₂, with subscripts modulo seven. Select a class of minimum degree and write the seven sizes cyclically as (a,b,c,x,y,z,v), with the selected class b. Put s=a+b+c≤k+1. The seven even-distance constraints include

    x+v≤k,   y+a≤k,   y+b≤k,   z+b≤k,   z+c≤k.

Consequently n≤3k+s−max(a,b)−max(b,c). Since max(a,b)≥(2a+b)/3 and max(b,c)≥(b+2c)/3, the two maxima sum to at least 2s/3. The claimed bound follows. This proof allows a unique vertex of degree below k.

**Equality in the unrounded bound.** Up to rotating or reversing the classes, equality n=(10k+1)/3 holds exactly for the following sizes in the same cyclic order:

    (a,a,a,x,2a−1,2a−1,v),     k=3a−1,
    x+v=3a−1,                    a≤x,v≤2a−1.

Indeed equality in the weighted maxima forces a=b=c, and all the other displayed inequalities force s=k+1, x+v=k, and y=z=k−a. The remaining two even-distance constraints are a+x≤k and c+v≤k, equivalent to the stated interval. Conversely, these sizes satisfy all seven even-distance constraints. All degrees are at least 3a−1, which is attained throughout the central size-a class. For a≥2 this class already has at least two vertices; for a=1 the graph is C₇. In particular the earlier examples n=20t+7,k=6t+2 attain the exact unrounded bound.

**Attaining the rounded bound.** The table gives one equality construction for each feasible value of k. The seven entries are always in cyclic order (a,b,c,x,y,z,v).

| k | Parameter | Cyclic class sizes | Order |
|---|---:|---|---:|
| 3h | h≥2 | (h+1,h,h,h+1,2h−1,2h,2h−1) | 10h |
| 3h+1 | h≥1 | (h+1,h,h+1,h+1,2h,2h,2h) | 10h+3 |
| 3h+2 | h≥0 | (h+1,h+1,h+1,h+1,2h+1,2h+1,2h+1) | 10h+7 |

In each row the triples centered at b and c have sum exactly k+1, so at least two distinct vertices have degree k. Every other consecutive triple has sum at least k+1. The seven cap inequalities are x+v, y+a, z+b, v+c, a+x, b+y, c+z≤k; substitution in the three rows verifies them all. The listed orders equal ⌊(10k+1)/3⌋.

**Small parameters.** Every vertex has degree at least two. At k=2, all class sizes equal one since each occurs in an even-distance count alongside another positive size. At k=3, every class has size one or two. Two size-two classes cannot be at cyclic distance three: their combined sizes would be the four vertices at distance two from the class lying two index steps from both. Thus all size-two classes are contained in three consecutive classes. To see this, if two of them are at distance two, every class within distance two of both lies on their short three-class segment. Otherwise there are at most two such classes and they are adjacent. Two distinct classes outside the closed neighborhood of that three-class segment now have both neighbors and themselves of size one. Each supplies a degree-two vertex, contrary to second-smallest degree three.
