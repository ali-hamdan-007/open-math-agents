import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Graph189SixIndexOrder

/-- The six-index order bound conflicts with integer maximum-degree width
at every remaining degree from 19 through 25. Each finite comparison uses
the least admissible order, so the quantified graph order is unbounded. -/
theorem impossible {k n e w : ℤ} (small : 19 ≤ k) (large : k ≤ 25)
    (lower : 7*(k-4)-1 ≤ n) (ep : 0 ≤ e) (em : e ≤ 2*k)
    (width : 2*(n-2*k)+k*e ≤ (k+1)*w)
    (budget : w*(n-2*k-e-2) ≤ k*(k+e)) : False := by
  let b := 7*(k-4)-1
  have bound : b ≤ n := lower
  have wp : 0 ≤ w := by
    by_contra! neg
    have bad := mul_neg_of_pos_of_neg (by omega : 0 < k+1) neg
    have plus := mul_nonneg (by omega : 0 ≤ k) ep
    omega
  have reduced := mul_le_mul_of_nonneg_left
    (by omega : b-2*k-e-2 ≤ n-2*k-e-2) wp
  have cap := reduced.trans budget
  have wit : 2*(b-2*k)+k*e ≤ (k+1)*w := by omega
  dsimp [b] at cap wit
  clear budget width reduced lower bound wp b n
  interval_cases k <;> norm_num at em cap wit <;> interval_cases e <;> omega

#print axioms impossible
end Graph189SixIndexOrder
