# Distance two alone permits a nontraceable interval graph with a cut vertex

Start with a central vertex a and a leaf z adjacent to a. Extend two additional arms from a. Each consists of five cliques with orders 2,2,1,3,2 in order, with complete joins between consecutive cliques and a complete join from a to the first clique. There are 22 vertices. The graph is interval: take base intervals [i,i+1] at the vertices of an eleven-vertex path for i=0,...,10, with a at i=5. Add z as the singleton interval [5.5,5.5]. Duplicate each arm interval as many times as its clique size.

| Vertex type | Degree | Number at distance two | Number at positive even distance |
|---|---:|---:|---:|
| a | 5 | 4 | 10 |
| z | 1 | 4 | 10 |
| Arm clique 1 | 4 | 4 | 9 |
| Arm clique 2 | 4 | 4 | 9 |
| Arm clique 3 | 5 | 4 | 10 |
| Arm clique 4 | 5 | 2 | 8 |
| Arm clique 5 | 4 | 1 | 9 |

Both arms are identical. Deleting a leaves three components, precluding a spanning path. All vertices have at most four at distance two, and z is the sole vertex of degree less than four.
