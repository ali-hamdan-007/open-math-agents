import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Basic

namespace Graph189SeparatorCounts

/-- A cut of size s sees one high neighbor in each of s+1 components.
The two inequalities summarize the disjoint distance-two counts at the
anchor and at its chosen neighbors. -/
theorem second_degree_le_cut_add_one {s k A : ℤ} (hs : 3 ≤ s)
    (internal : (s+1)*(k-s+1) ≤ A+k)
    (external : s*A ≤ (s+1)*k) : k ≤ s+1 := by
  by_contra! h
  have hk : 0 ≤ k-s-2 := by omega
  have coeff : 0 ≤ s*s-s-1 := by
    nlinarith [mul_nonneg (show 0 ≤ s-3 by omega) (show 0 ≤ s+2 by omega)]
  have extra := mul_nonneg hk coeff
  have hsum := mul_le_mul_of_nonneg_left internal (show 0 ≤ s by omega)
  nlinarith [mul_nonneg (show 0 ≤ s-3 by omega) (show 0 ≤ s+1 by omega)]

theorem two_cut_three_components {k A : ℤ}
    (internal : 3*(k-1) ≤ A+k) (external : 2*A ≤ 3*k) : k ≤ 6 := by
  linarith

theorem two_cut_four_components {k A : ℤ} (hk : 3 ≤ k)
    (internal : 4*(k-1) ≤ A+k) (external : 3*A ≤ 4*k) : False := by
  linarith

/-- A low singleton sees all ports of the other components at distance two. -/
theorem singleton_degree_le_cut_add_one {s k : ℤ} (hs : 5 ≤ s)
    (bound : (s-2)*k ≤ s*(s-1)) : k ≤ s+1 := by
  by_contra! h
  have hmul := mul_nonneg (show 0 ≤ s-2 by omega) (show 0 ≤ k-s-2 by omega)
  nlinarith

end Graph189SeparatorCounts

#print axioms Graph189SeparatorCounts.second_degree_le_cut_add_one
#print axioms Graph189SeparatorCounts.singleton_degree_le_cut_add_one
