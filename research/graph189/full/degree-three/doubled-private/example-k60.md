# The distance-two relaxation admits the doubled-private triangle

For k=60 there is a connected graph on 185>180 vertices with the doubled-private triangle incidence, T singleton, eccentricity three at z, second-smallest degree 60, and at most 60 vertices at distance exactly two from every vertex. Thus the distance-two-only hypotheses in residual.md cannot exclude this entire template. Under the full even-distance hypothesis this example fails: one private middle has 60 vertices at distance two and another 60 at distance four. The example itself has a spanning path.

The vertices are z, anchors A,B,C, private middles p,q,b,c, common middles w_0,...,w_55, remotes x_0,...,x_59 and y_0,...,y_59, and the additional remote t. Make each of {A,B,C}, W, X and Y a clique. Join z to all anchors, all anchors to W, A to p,q, B to b and C to c. Further neighbors are listed below; indices are inclusive. All unlisted edges are absent.

| Vertex | Additional neighbors |
|---|---|
| p | w_1 through w_24, w_30 through w_55, x_0 through x_14 |
| q | w_0 through w_24, y_0 through y_36 |
| b | w_25 through w_29, x_5 through x_59 |
| c | w_30 through w_55, y_24 through y_59 |
| t | all W, p, b, x_5 through x_12 |

The script doubled-distance-two-witness.py constructs all 5,573 edges, verifies the exact root layers and masks, checks singleton T and every distance-two count by breadth-first search, and verifies the spanning path. A separate Floyd–Warshall calculation agreed on all 34,225 ordered distances. The path in order is q, Y in increasing order, c,C,z,B,b, X in decreasing order, p,t, W in increasing order, A.
