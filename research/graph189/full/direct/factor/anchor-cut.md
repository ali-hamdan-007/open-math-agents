# A distance-two bound at an anchor of any separator

Let G be 2-connected, let all but at most one vertex have degree at least k and suppose each vertex has at most k vertices at distance two. Let S be a vertex cut of size s. Fix an anchor u in S and t≥2 distinct components C_i of G−S in which u has a high neighbor y_i. Write D_i=N(u)∩C_i, X_i=N₂(u)∩C_i and a_i=|N(y_i)∩S|. The closed internal neighborhood of y_i has at least k+1−a_i vertices, all in D_i∪X_i. In addition, y_i sees the union of the other D_j at distance two via u. Therefore

(t−1)Σ_i|D_i|≤tk,     Σ_i|X_i|≤k,

Σ_i a_i ≥ t(k+1)−k−⌊tk/(t−1)⌋.

For t=3 the bound is Σ_i a_i≥3+ceil(k/2), hence k≤6(s−1). If c(G−S)≥s+2, discard the possible component containing an exceptional low vertex. Each remaining component meets at least two distinct anchors by 2-connectivity, so there are at least 2(s+1) incidences, giving a common anchor of three wholly high components. Thus every component-count certificate of nontraceability c(G−S)>s+1 requires s≥1+ceil(k/6). This holds without upper-order or diameter hypotheses.
