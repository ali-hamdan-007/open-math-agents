# Moderate-order completion certificates

The four traces files contain explicit certificates for all 188 labelled partial graphs produced by the independent attachment enumerator. Vertices 0 through p−1 are the deletion path in order, p through n−2 are exterior vertices, and n−1 is z. Every adjacency matrix is a list of natural numbers, with bit j of row i indicating adjacency to j. A contact mask instead records positions on the deletion path. The upper graph adds every optional path chord and every optional edge at z.

| Degree | Intervals | Mandatory G path | Cut after one deletion | Insufficient upper degree | Excess forced distance-two vertices | Forbidden edges with path lists |
|---|---:|---:|---:|---:|---:|---:|
| 3 | 9 | 8 | 0 | 0 | 1 | 1 |
| 4 | 30 | 7 | 20 | 0 | 3 | 165 |
| 5 | 51 | 7 | 41 | 0 | 3 | 415 |
| 6 | 98 | 4 | 83 | 7 | 4 | 1056 |

A forbidden edge carries an ordered list of distinct vertices forming a path in the lower graph with that one edge added. A G witness has at least n−ceil(k/2)−1 vertices. An H witness avoids z and has at least p+1 vertices. Cut leaves specify both sides of a partition after deleting the stated vertex. A degree leaf lists every remaining upper neighbor. At an even-distance leaf each pair gives a target and a middle vertex. The two lower edges via the middle vertex exist and the upper graph lacks the direct edge to the target. The targets are distinct. No trace needs a forced edge or a case split.

Run the following from this directory to regenerate the inputs and witnesses, replay them, and regenerate the relabeling tables.

```sh
python export_patterns.py
python make_traces.py
python verify_traces.py
python orbit_lookup.py
```

The exporter runs the independently written C++17 enumeration in attachment-enumerator.cpp. The replay needs Python’s standard library. It reconstructs the full initial interval from the exterior and contact masks, checks every path edge individually, removes each forbidden edge in order, and checks the stated terminal obstruction. It performs no graph search.

The relabeling tables associate every surviving ordering of the exterior and each path orientation to a named initial interval. The coverage of all eligible actual graphs by these attachment patterns is a separate theorem. The concrete rejection certificates address the listed intervals.

Pinned Lean 4.33.1 has checked all nine concrete degree-three intervals as Rejection theorems with warnings as errors. Each theorem reports only propext, Classical.choice and Quot.sound. See Graph189ModerateK3.lean and k3-lean.log.
