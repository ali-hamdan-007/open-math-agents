# Remaining W(3,13) reduction cases

The current R2 file in [PR #4300](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4300) defines H3 by the second-difference signs −,+ and the lexicographic normalization on the sums of reflected heights. There are 4,924 normalized tuples, including 82 fixed by reflection. The 302 checked forbidden four-red sets fit exactly the six adjacent ascending tuples already proved. Red/blue unit propagation with all 302 clauses eliminates no additional H3 tuple. The remaining 4,918 tuples span 378 height-difference classes. In particular, there are 36 remaining ascending alternating tuples with a height gap greater than one.

The more local target is the endpoint-obstruction pair in proposed R1.H2.R1 [PR #5179](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5179). The exact SAT inputs are:

| Hypothesis | Window | Required red positions | Required blue positions |
| --- | ---: | --- | --- |
| H1 | 158 | 75 | 76–81 |
| H2 | 159 | 0, 77 | 78–81 |
| H3 | 159 | 76, 158 | 77–80 |
| H4 | 160 | 77 | 0, 78–81, 159 |

All indices in the table start at zero inside the indicated window. For H2, failure of an interior red triple obstruction allows position 0 to be colored red, producing an avoiding coloring in the 159-point window. For H3, the analogous argument colors position 159 red and starts the 159-point window at 1. For H4, failure of both blue endpoint obstructions allows both endpoints to be blue. A forbidden progression cannot span both endpoints since their distance 159 is divisible by neither 2 nor 12. H1 translates the 158-point interior by one.

CaDiCaL returned UNSAT for H2 and H3 within 15 seconds. H1 and H4 reached the 15-second limit. The trusted bit-mask proof search reached its 800,000-node cap on all four. Untrimmed binary LRAT traces for H2 and H3 were 35,890,375 and 38,619,279 bytes respectively. Adding all transferred short-window clauses gave traces of 39,536,940 and 36,478,549 bytes. The traces were measured through a named pipe and discarded. These SAT results identify concrete candidate substeps. No Lean certificate for them was constructed.

The previously submitted direct proofs [#5141](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5141) and [#4877](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4877) concern R1.H3's larger central gaps. They address a different hypothesis from R2.H3 and the endpoint-obstruction pair.

## Reproduce

```sh
python3 assess_h3.py
python3 probe_r1.py /absolute/path/to/cadical
python3 probe_r1.py /absolute/path/to/cadical --seconds 22 --lrat-size
python3 probe_r1.py /absolute/path/to/cadical --seconds 22 --lrat-size --learned
```

The learned-clause option transfers each checked window only when it fits inside the target interval. All probes are local. They produce no retained LRAT proof files.
