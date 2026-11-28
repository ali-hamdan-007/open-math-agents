import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum

namespace Graph189QuarterOrder

/-- The quarter-index lower order gives the two linear comparisons used
when eliminating maximum-degree excess from the width inequality. -/
theorem lower_estimates {k n : ℕ} (large : 26 ≤ k)
    (lower : ((k+2)/4+1)*(k-(k+2)/4+2) ≤ n+1) :
    let t : ℤ := n-2*(k:ℤ)
    4*(k:ℤ) ≤ t ∧ (k:ℤ)*(k+1) < 8*(t-2) := by
  let l := (k+2)/4
  change (l+1)*(k-l+2) ≤ n+1 at lower
  have lk : l ≤ k := by dsimp [l]; omega
  have a : k+3 ≤ 4*(l+1) := by dsimp [l]; omega
  have b : 3*k+6 ≤ 4*(k-l+2) := by dsimp [l]; omega
  have product := Nat.mul_le_mul a b
  have scaled : (k+3)*(3*k+6) ≤ 16*(n+1) := by nlinarith only [product,lower]
  let t : ℤ := n-2*(k:ℤ)
  have base : 4*(k:ℤ) ≤ t := by
    by_cases big : 30 ≤ k
    · zify at big scaled
      dsimp [t]
      nlinarith only [scaled,mul_nonneg (show 0 ≤ (k:ℤ)-30 by omega) (show 0 ≤ 3*(k:ℤ)+9 by omega)]
    · have limit : k ≤ 29 := by omega
      have finite_lower : ((k+2)/4+1)*(k-(k+2)/4+2) ≤ n+1 := lower
      change 4*(k:ℤ) ≤ (n:ℤ)-2*k
      interval_cases k <;> norm_num at finite_lower ⊢ <;> omega
  have more : (k:ℤ)*(k+1) < 8*(t-2) := by
    zify at scaled
    dsimp [t]
    nlinarith only [scaled,mul_nonneg (show 0 ≤ (k:ℤ)-26 by omega) (show 0 ≤ (k:ℤ)+7 by omega)]
  exact ⟨base,more⟩

/-- A lower order at one quarter of the second-smallest degree already
contradicts the two actual maximum-degree width estimates. -/
theorem impossible {k n : ℕ} (large : 26 ≤ k)
    (lower : ((k+2)/4+1)*(k-(k+2)/4+2) ≤ n+1) {e w : ℤ}
    (ep : 0 ≤ e) (em : e ≤ 2*k)
    (width : 2*((n:ℤ)-2*k)+k*e ≤ (k+1)*w)
    (budget : w*((n:ℤ)-2*k-e-2) ≤ k*(k+e)) : False := by
  let t : ℤ := n-2*(k:ℤ)
  obtain ⟨base,more⟩ := lower_estimates large lower
  change 4*(k:ℤ) ≤ t at base
  change (k:ℤ)*(k+1) < 8*(t-2) at more
  change 2*t+k*e ≤ (k+1)*w at width
  change w*(t-e-2) ≤ k*(k+e) at budget
  have p : 0 ≤ t-e-2 := by omega
  have lft := mul_le_mul_of_nonneg_right width p
  have rgt := mul_le_mul_of_nonneg_left budget (show 0 ≤ (k:ℤ)+1 by omega)
  have coeff : 0 ≤ ((k:ℤ)-2)*t-k*(e+k+3) := by
    nlinarith only [mul_nonneg (show 0 ≤ (k:ℤ)-2 by omega) (sub_nonneg.mpr base),
      mul_nonneg (show 0 ≤ (k:ℤ) by omega) (sub_nonneg.mpr em),
      mul_nonneg (show 0 ≤ (k:ℤ) by omega) (show 0 ≤ (k:ℤ)-11 by omega)]
  have cubic : 2*t*(t-2) ≤ (k:ℤ)^2*(k+1) := by
    nlinarith only [lft,rgt,mul_nonneg ep coeff]
  have smaller := mul_le_mul_of_nonneg_right base (show 0 ≤ 2*(t-2) by omega)
  have bigger := mul_lt_mul_of_pos_left more (show 0 < (k:ℤ) by omega)
  nlinarith only [cubic,smaller,bigger]

#print axioms impossible
end Graph189QuarterOrder
