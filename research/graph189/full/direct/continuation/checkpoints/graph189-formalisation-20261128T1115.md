# Graph 189 formalisation checkpoint — 28 November 2026 11:15 UTC

The exact full-parent lease remained live throughout this wave. This checkpoint
records local research only; it is not an official checker verdict and the exact
parent remains open.

Pinned Lean 4.33.1, warning-as-error, standard axioms only:

- `Graph189ContactGroupCensus.rows_uniform`;
- `protected_gap_sum` and `two_full_gaps`;
- `width_sum` and the actual-path `path_group_census`;
- the pinned protected-interval detour lemmas;
- `uniform_of_protected_census`, including the equality case `u = |E|`;
- `two_swappable_intervals`;
- `full_exterior_splice`, `full_gap_dist_two`, and
  `even_budget_of_full_gaps`.

Source-only work preserved in the accompanying archive includes the final
minimum-deletion composition, the ordinary longest-path gap bridge, the exact
two-cut routing wrappers, the five-way split of the connectivity-three density
module, and the degree-18 connectivity-four row certificate. Those files need
their stated compilation order and must not be cited as kernel theorems yet.

The independently audited kappa-two, kappa-three, kappa-four, and one-below-half
paper arguments reproduce coverage already recorded in the research frontier;
their value here is proof engineering and independent checking, not an
originality claim.
