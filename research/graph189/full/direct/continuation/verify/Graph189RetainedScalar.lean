import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Real.Basic

namespace Graph189RetainedScalar

/-- A uniform strict order-coefficient improvement from the maximum-degree width
inequality and the necessary rooted local Ore degree excess. Here m = n - 2*k,
e = maximum degree - k, and c counts high vertices in the third layer. -/
theorem order_gap {k m e c : ℝ} (hk : 100 ≤ k) (hm : 100*k ≤ m)
    (he : 0 ≤ e) (he' : e ≤ 2*k) (hc : m ≤ c+e+2)
    (hore : m-k-1 ≤ k*e)
    (hwidth : c*(2*m+k*e) ≤ k*(k+1)*(2*k+e)) :
    4*m^2 ≤ 3*k^3 := by
  have kpos : 0 < k := by linarith
  have cpos : 0 ≤ c := by linarith
  have mpos : 0 ≤ m := by linarith
  have hrow : 97/100*m ≤ c := by linarith
  have hrow' : 97*k ≤ c := by linarith
  have upper := mul_le_mul_of_nonneg_left (show 2*k+e ≤ 4*k by linarith)
    (show 0 ≤ k*(k+1) by positivity)
  have lower := mul_le_mul_of_nonneg_right hrow' (show 0 ≤ k*e by positivity)
  have ec : 97*k^2*e ≤ 4*k^2*(k+1) := by
    nlinarith only [lower, upper, hwidth, mul_nonneg cpos mpos]
  have ee : e ≤ k/20 := by
    by_contra! bad
    have step := mul_lt_mul_of_pos_right bad (show 0 < 97*k^2 by positivity)
    have step₂ := mul_nonneg (show 0 ≤ 17*k-80 by linarith) (sq_nonneg k)
    nlinarith only [step, step₂, ec]
  have hfactor : 298/100*m ≤ 2*m+k*e := by linarith
  have lo := mul_le_mul hrow hfactor (show 0 ≤ 298/100*m by positivity) cpos
  have hi := mul_le_mul_of_nonneg_left (show 2*k+e ≤ 205/100*k by linarith)
    (show 0 ≤ k*(k+1) by positivity)
  have hi' := mul_le_mul_of_nonneg_right (show k+1 ≤ 101/100*k by linarith)
    (show 0 ≤ 205/100*k^2 by positivity)
  nlinarith only [lo, hi, hi', hwidth, mul_nonneg (sq_nonneg k) kpos.le]

#print axioms order_gap
end Graph189RetainedScalar
