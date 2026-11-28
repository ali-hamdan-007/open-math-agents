# Uniform estimates near equality in the endpoint bound

Retain `endpoint-linear-growth.md` and put s=2t−k≥0. Assume k≥t+2. Fix a compatible pair of high endpoints u,v at odd distance in a single rotation class and take a realization from u to v. Let B be the set of non-R path blocks, including singletons. The number b=|B| equals k+t−h, where h is the number of consecutive R-R edges. The earlier proof gives q_u,q_v≥k−t=t−s and h≥q_u+q_v, so b≤t+s. Both endpoints touch the entry of each block they see and never a common vertex. Thus blocks touched by both are nonsingletons. Let Q be this set of shared blocks and write Q₀=|Q|. The two sets of blocks visited by u,v have total size at least 2k−q_u−q_v, and their union has size at most b. Hence

    Q₀ ≥ 2k−q_u−q_v−b ≥ k−t = t−s.

Every high endpoint w touches at least k−q_w≥k−t=t−s different blocks, so it misses at most 2s blocks in total. It touches at least t−3s of Q. On all of those blocks the second vertices from its own tips are forced members of F_w, all distinct. At most 3s other positive even vertices outside R remain from w. In particular every high attainable endpoint is at odd distance from every omitted vertex except at most 3s of them. If one of w's high R-neighbors chooses the opposite end in a shared block of length at least three, that opposite tip gives a further even witness: it is not w's second vertex in the same block, nor a second vertex in any other block. Accordingly across all its R-neighbors, w can be involved in opposite choices in at most 3s such long shared blocks on which it actually chooses a tip. The final two statements use the bound only when its right side is informative.

## Two groups of near-complementary signatures

Label the ends of each block in Q. A high w determines a partial binary word on the Q₀ blocks, with a missing symbol if it touches neither end. Complete its at most 2s missing coordinates arbitrarily. The words of u,v are exact complements. When two high endpoints have odd distance ≥3, they do not share a neighbor. Wherever their words both come from actual contacts, they must therefore be opposite. Their completed words have Hamming distance at most 4s from being complements.

For each high w, at most t of the other high members of R are adjacent to w, and at most k−(t−3s)=t+2s have positive even distance from it. There are at least k+t=3t−s high endpoints. Hence at least M=t−3s−1 high endpoints are at odd distance ≥3 from w. If M>0, the Hamming ball of radius 4s around the bitwise complement of w's word contains at least M high endpoints, with multiplicity. A ball of radius 8s around w's own word also contains at least M: choose one of those odd partners, and then take its odd partners.

If t>11s+5, every high endpoint's completed word is within 16s of u's or v's word. Indeed a high word w farther than 16s from both would give four centers u,v,w and the complement of w, pairwise farther than 16s. The cross distances have this bound by the contrary assumption and the complement isometry, and the two antipodal distances are Q₀, which exceeds 32s since the distances of w to the antipodal pair u,v sum to Q₀. The four radius-8s balls are disjoint. Each would contain at least M high endpoints, impossible since 4M>3t−s+1=|R|. This is a stability statement about the incidence of attainable endpoints with fixed path blocks. It does not imply that the two groups are connected in G[R].

## At least half the shared blocks have two vertices, up to an additive error

Assume t>11s+5. Let ℓ be the number of shared blocks with at least three vertices. Then

    ℓ ≤ (t+s)/2+1+80s.

Consequently at least t/2−82s−1 shared blocks have exactly two vertices. If ℓ≤39s the upper bound is immediate. Otherwise the two clusters are disjoint: on the ℓ long coordinates, two members in opposite clusters disagree in at least ℓ−32s completed bits and in at least ℓ−36s actual tips after their erasures. Their being adjacent would use more than 3s extra even witnesses at one of them, impossible. Thus there is no high G[R]-edge across clusters. Each high endpoint has at least t−2s−1 high neighbors in its own cluster, since it has at most b≤t+s non-R neighbors and degree at least 2t−s.

Call a long coordinate impure if some high endpoint chooses the opposite tip to its cluster center there (a missing contact alone is allowed). For each impure coordinate take a high endpoint that flips its cluster's bit. Every one of its at least t−2s−1 high R-neighbors lies in the same cluster. Such a neighbor either flips or misses the coordinate, or it touches the usual tip and sees the opposite tip at distance two via the selected flipping endpoint. For each high neighbor there are at most 18s missed-or-flipped coordinates (16s Hamming errors and 2s erasures) and at most 3s long coordinates with an opposite-tip charge as proved above. Thus the number I of impure coordinates satisfies

    I(t−2s−1) ≤ 21s |R_high| ≤ 21s(3t−s+1),

and I≤80s follows from t>11s+5. For each pure long shared block its entry on the u-to-v realization touches u and its exit touches v. A high R neighbor of the entry along the path must belong to the u cluster. A high R neighbor of the exit belongs to the v cluster. Between consecutive pure long blocks the path must cross back from the v cluster to the u cluster. If that interval contains neither a different block nor the low vertex, it would require a forbidden high cross-cluster R-edge. The separating intervals are disjoint, so the number L=ℓ−I of pure long blocks satisfies L−1≤(b−L)+1. Hence 2L≤b+2≤t+s+2 and the claim follows.
