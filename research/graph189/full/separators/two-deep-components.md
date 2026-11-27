# A separating pair containing the unique low vertex

Let G be a finite simple 2-connected graph with second-smallest degree k and at most k other vertices at positive even distance from any vertex. Suppose a 2-cut {z,q} with deg(z)=δ<k leaves exactly two components C₁,C₂, each meeting the two anchors. Then δ=k−1 and G has a Hamilton path. If both components contain a nonport, each has order at most 2k−2. If one has no nonport, the whole graph has order at most 2k+2. The theorem has no initial order assumption.

Each component meets both anchors z and q by 2-connectivity. It has distinct vertices usable as contacts for z and q whenever it contains a nonport, since otherwise its single contact would disconnect the nonempty interior from the rest of the graph. In Cᵢ write Pᵢ for the set of vertices adjacent to at least one anchor, Rᵢ=Cᵢ minus Pᵢ, and aᵢ for the number adjacent to z. Every component vertex is high, that is, has degree at least k.

## The low anchor forces two common contacts

Let e indicate adjacency of z,q. Let uᵢ indicate the presence in Cᵢ of some vertex adjacent to both anchors, and put u=u₁+u₂. Pick a z-contact vᵢ in each component, using a common contact whenever available. In its closed neighborhood at least k−uᵢ vertices belong to Cᵢ, since it has at least k+1 vertices in its closed neighborhood and only z and potentially q can occur outside Cᵢ. Of these, all except at most aᵢ are at distance two from z. Also a₁+a₂=δ−e. If u=0, the two disjoint counts give k≥2k−δ+e, impossible. Thus u≥1, and q itself supplies an additional witness when e=0, via a common contact. We now have

    k ≥ 2k − (δ−e) − u + (1−e) = 2k − δ − u + 1.

Since δ≤k−1 and u≤2, we conclude δ=k−1 and u=2. This conclusion holds even without the nonempty-interior assumption.

Equality in the displayed count also implies that every common contact in either component has ambient degree exactly k. A common contact of larger degree could be chosen as vᵢ, increasing that component's lower bound by at least one.

## A component that contains only ports

Suppose Cⱼ consists entirely of ports. Its vertices are high, so |Cⱼ|≥k−1 by counting possible neighbors including the two anchors. A common contact x in the other component Cᵢ sees all of Cⱼ at distance two, so |Cⱼ|≤k and at most one vertex of Cᵢ can lie at distance two from x.

The torso on Cᵢ,z,q obtained by adding the edge zq if absent is 2-connected. After deleting any one vertex, paths in the 2-connected ambient graph project to walks in this torso by replacing excursions through Cⱼ by the edge zq or by deleting return excursions. Torso distances from x to its vertices agree with ambient distances: both excursions through Cⱼ and any use of a new edge zq in a torso path can be bypassed by starting directly from x at the last anchor on that path, since x is adjacent to both. Its entire distance-two layer in the torso thus has size at most one, as the anchors are at distance one. No vertex can lie beyond that layer: the layer would otherwise be a separator of size at most one in the 2-connected torso. The k neighbors of x include the two anchors, leaving k−2 neighbors inside Cᵢ. There is at most one more vertex there apart from x. Hence |Cᵢ|≤k and |G|≤2k+2, giving traceability by the known order theorem.

## Bounds when both components contain a nonport

By the previously proved distance-five endpoint theorem and the general diameter bound, every two high vertices have distance at most four. The distance between two nonports in opposite components is at least four, since any connecting path meets the anchors. Thus every such pair has distance exactly four. In particular any nonport is at distance two from at least one anchor (take a length-four path to an opposite nonport).

A common contact in Cⱼ sees every port in Cᵢ at distance two, so |Pᵢ|≤k. A nonport in Cⱼ sees all |Rᵢ| nonports at distance four and at least one anchor at distance two. Hence |Rᵢ|≤k−1. If |Pᵢ|=k, a common contact of Cⱼ exhausts its budget on Pᵢ. It is therefore adjacent to the entirety of Cⱼ, since any nonneighbor would yield an internal distance-two witness along a shortest internal path to that nonneighbor. Thus a nonport in Cⱼ sees both anchors at distance two, giving |Rᵢ|≤k−2. In either case |Cᵢ|≤2k−2.

## Rooted paths on the two sides

For C₁ use the graph induced on C₁,z,q, with a new leaf adjacent only to q. Its order is |C₁|+3, and each C₁ vertex has degree at least k since no original neighbor was lost. The ordinary path-closure rule preserves existence of a Hamilton path when adding an edge between two nonneighbors with degree sum at least the order minus one. Consequently every missing edge within C₁ may be added, since 2k≥|C₁|+2. In the completed graph start at the leaf, traverse q, use the clique C₁ between distinct original q- and z-contacts, and finish at z. There is therefore a spanning path in the original augmented graph. Its leaf endpoint forces its successor to be q. Removing the leaf gives a spanning path of C₁ together with z,q having endpoint q. The other endpoint need not still be z.

For C₂ use the graph induced on C₂,q, with a fresh leaf adjacent only to q. The closure threshold is |C₂|+1. Each component vertex has degree at least k−1, since only the neighbor z could be lost. If |C₂|≤2k−3 the same closure rule completes C₂ immediately. If |C₂|=2k−2, at most k−1 of its vertices see z, since z has total degree k−1. At least k−1 vertices in C₂ therefore have degree at least k in the augmented graph and can successively join every vertex in C₂ by the closure rule. In the resulting graph choose k−1 of these universal vertices as U. Its complement within C₂ likewise has size k−1, and all edges between the two sets are present. Consequently from any original q-contact in C₂ there is a spanning path in C₂ by alternating between the two equal-sized sets. Prepending the leaf and q gives a spanning path in the completed augmented graph. The traceability-preserving closures give one also in the original graph, where the leaf forces q as its successor. Delete the leaf. The resulting two paths overlap only at q and have it as an endpoint. Their union is a spanning path of G.

The proof uses the established high-vertex distance bound only for the comparison of opposite nonports. The marker argument uses only ordinary path closure.
