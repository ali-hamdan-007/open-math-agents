import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos307Structure

/-- If c ≤ d, the smaller factor lies just above the product-to-sum ratio.
Uniform bounds on that ratio and on the sum give an explicit narrow interval. -/
theorem smaller_factor_interval {c d H L : ℚ} (hc : 0 < c) (hcd : c ≤ d)
    (hL : 0 < L) (hLsum : L ≤ c + d) (hH : c * d / (c + d) ≤ H) :
    c * d / (c + d) < c ∧ c ≤ H + 4 * H ^ 2 / L := by
  let R : ℚ := c * d / (c + d)
  change R < c ∧ c ≤ H + 4 * H ^ 2 / L
  have hd : 0 < d := hc.trans_le hcd
  have hs : 0 < c + d := add_pos hc hd
  have hR : 0 < R := div_pos (mul_pos hc hd) hs
  have hh : 0 < H := hR.trans_le hH
  have hdiff : c - R = c ^ 2 / (c + d) := by
    dsimp [R]
    field_simp
    ring
  have h2 : c ≤ 2 * R := by
    change c ≤ 2 * (c * d / (c + d))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hs).mpr
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hcd)]
  have h2H : c ≤ 2 * H := by linarith
  have hsq : c ^ 2 ≤ 4 * H ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h2H) (show 0 ≤ 2 * H + c by linarith)]
  have hupper : c ^ 2 / (c + d) ≤ 4 * H ^ 2 / L :=
    (div_le_div_of_nonneg_right hsq hs.le).trans
      (div_le_div_of_nonneg_left (by positivity) hL hLsum)
  have hstrict : 0 < c ^ 2 / (c + d) := by positivity
  constructor <;> linarith

/-- Uniform interval for the smaller right closing denominator when both left
closing denominators are at least alpha. Here k*alpha² is any lower bound on
the right pair product. This is the rational tail cutoff used in the search. -/
theorem two_pair_tail_interval {sl sr alpha k a b c d : ℚ}
    (hsl : 0 < sl) (ha : alpha ≤ a) (hab : a ≤ b) (halpha : 0 < alpha)
    (hk : 0 < k) (hc : 0 < c) (hcd : c ≤ d)
    (hprod : k * alpha ^ 2 ≤ c * d)
    (hdelta : 0 < 1 / (sl + 2 / alpha) - sr)
    (hsum : 1 = (sl + 1 / a + 1 / b) * (sr + 1 / c + 1 / d)) :
    let W := 1 / (1 / sl - sr)
    let H := 1 / (1 / (sl + 2 / alpha) - sr)
    W < c ∧ c ≤ H + 4 * H ^ 3 / (k * alpha ^ 2) := by
  let ls : ℚ := sl + 1 / a + 1 / b
  let mx : ℚ := sl + 2 / alpha
  let R : ℚ := c * d / (c + d)
  let W : ℚ := 1 / (1 / sl - sr)
  let H : ℚ := 1 / (1 / mx - sr)
  change W < c ∧ c ≤ H + 4 * H ^ 3 / (k * alpha ^ 2)
  change 0 < 1 / mx - sr at hdelta
  have ha0 : 0 < a := halpha.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hd0 : 0 < d := hc.trans_le hcd
  have hcd0 : 0 < c + d := add_pos hc hd0
  have hls : sl < ls := by
    dsimp [ls]
    linarith [one_div_pos.mpr ha0, one_div_pos.mpr hb0]
  have hls0 : 0 < ls := hsl.trans hls
  have hmx : ls ≤ mx := by
    dsimp [ls, mx]
    rw [show (2 : ℚ) / alpha = 1 / alpha + 1 / alpha by ring]
    linarith [one_div_le_one_div_of_le halpha ha,
      one_div_le_one_div_of_le halpha (ha.trans hab)]
  have hmx0 : 0 < mx := hls0.trans_le hmx
  have hlsrec : 1 / ls = sr + 1 / c + 1 / d := by
    apply (div_eq_iff hls0.ne').mpr
    simpa [ls, mul_comm] using hsum
  have hR : R = 1 / (1 / ls - sr) := by
    have hratio : 1 / ls - sr = (c + d) / (c * d) := by
      rw [hlsrec]
      field_simp
      ring
    rw [hratio]
    dsimp [R]
    field_simp
  have hdlo : 1 / mx - sr ≤ 1 / ls - sr :=
    sub_le_sub_right (one_div_le_one_div_of_le hls0 hmx) _
  have hdhi : 1 / ls - sr < 1 / sl - sr :=
    sub_lt_sub_right (one_div_lt_one_div_of_lt hsl hls) _
  have hdmid : 0 < 1 / ls - sr := hdelta.trans_le hdlo
  have hW : W < R := hR.symm ▸ one_div_lt_one_div_of_lt hdmid hdhi
  have hH : R ≤ H := hR.symm ▸ one_div_le_one_div_of_le hdelta hdlo
  have hH0 : 0 < H := one_div_pos.mpr hdelta
  have hka : 0 < k * alpha ^ 2 := by positivity
  have hL : 0 < k * alpha ^ 2 / H := div_pos hka hH0
  have hr : k * alpha ^ 2 / H ≤ c + d := by
    apply (div_le_iff₀ hH0).mpr
    calc
      _ ≤ c * d := hprod
      _ = R * (c + d) := (div_mul_cancel₀ _ hcd0.ne').symm
      _ ≤ H * (c + d) := mul_le_mul_of_nonneg_right hH hcd0.le
      _ = _ := mul_comm _ _
  obtain ⟨hrc, hcH⟩ := smaller_factor_interval hc hcd hL hr hH
  refine ⟨hW.trans hrc, ?_⟩
  have he : 4 * H ^ 2 / (k * alpha ^ 2 / H) = 4 * H ^ 3 / (k * alpha ^ 2) := by
    field_simp
  rwa [he] at hcH

/-- In any completion of total mass at least two, four new denominators,
all at least a, fill a deficit at most 4/a. This bounds the smallest closing
prime without bounding any of the other three. -/
theorem smallest_closing_bound {base a b c d x y : ℚ}
    (ha : 0 < a) (hb : a ≤ b) (hc : a ≤ c) (hd : a ≤ d)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hprod : x * y = 1)
    (htot : x + y = base + 1 / a + 1 / b + 1 / c + 1 / d) :
    (2 - base) * a ≤ 4 := by
  have hm : 2 ≤ x + y := by
    by_contra! h
    have he := mul_pos (sub_pos.mpr h) (show 0 < 2 + (x + y) by linarith)
    nlinarith [sq_nonneg (x - y)]
  apply (le_div_iff₀ ha).mp
  rw [show (4 : ℚ) / a = 1 / a + 1 / a + 1 / a + 1 / a by ring]
  linarith [one_div_le_one_div_of_le ha hb, one_div_le_one_div_of_le ha hc,
    one_div_le_one_div_of_le ha hd]

#print axioms smaller_factor_interval
#print axioms two_pair_tail_interval
#print axioms smallest_closing_bound
end Erdos307Structure
