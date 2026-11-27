import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace TupleLogGap

/-- The normalized positive Pell factors have a strictly positive logarithmic gap
bounded by a constant times the inverse square of their common coordinate. -/
theorem simultaneous_gap (x y z : ℝ) (hx : 2 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (h₃ : y ^ 2 = 3 * x ^ 2 - 2) (h₈ : z ^ 2 = 8 * x ^ 2 - 7) :
    let Λ := Real.log ((x + y / Real.sqrt 3) / (x + z / Real.sqrt 8))
    0 < Λ ∧ Λ < (5 / 24) / x ^ 2 := by
  let a := y / Real.sqrt 3
  let b := z / Real.sqrt 8
  have hs₃ : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hs₈ : 0 < Real.sqrt 8 := Real.sqrt_pos.2 (by norm_num)
  have ha : 0 < a := div_pos hy hs₃
  have hb : 0 < b := div_pos hz hs₈
  have ha_sq : a ^ 2 = x ^ 2 - 2 / 3 := by
    dsimp [a]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), h₃]
    ring
  have hb_sq : b ^ 2 = x ^ 2 - 7 / 8 := by
    dsimp [b]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), h₈]
    ring
  have hxsq : 4 ≤ x ^ 2 := by nlinarith
  have ha_half : x / 2 < a := by
    by_contra! h
    have he := mul_nonneg (show 0 ≤ x / 2 - a by linarith)
      (show 0 ≤ x / 2 + a by linarith)
    nlinarith
  have hb_half : x / 2 < b := by
    by_contra! h
    have he := mul_nonneg (show 0 ≤ x / 2 - b by linarith)
      (show 0 ≤ x / 2 + b by linarith)
    nlinarith
  have hab : a - b = (5 / 24) / (a + b) := by
    apply (eq_div_iff (show a + b ≠ 0 by linarith)).2
    nlinarith
  have hapos : 0 < a - b := by
    rw [hab]
    exact div_pos (by norm_num) (by linarith)
  have hr : 1 < (x + a) / (x + b) := (one_lt_div (by linarith)).2 (by linarith)
  have hxsq_pos : 0 < x ^ 2 := by linarith
  have hprod : x ^ 2 < (a + b) * (x + b) := by
    have he := mul_lt_mul_of_pos_right (show x < a + b by linarith)
      (show 0 < x + b by linarith)
    have he' := mul_pos (show 0 < x by linarith) hb
    nlinarith
  have hconvert : (x + a) / (x + b) - 1 = (5 / 24) / ((a + b) * (x + b)) := by
    calc
      _ = (a - b) / (x + b) := by
        field_simp [show x + b ≠ 0 by linarith]
        ring
      _ = _ := by rw [hab, div_div]
  change 0 < Real.log ((x+a)/(x+b)) ∧ Real.log ((x+a)/(x+b)) < (5/24) / x ^ 2
  refine ⟨Real.log_pos hr, ?_⟩
  calc
    _ < (x + a) / (x + b) - 1 :=
      Real.log_lt_sub_one_of_pos (by linarith) (ne_of_gt hr)
    _ = _ := hconvert
    _ < _ := div_lt_div_of_pos_left (by norm_num) hxsq_pos hprod


/-- A rational interval certificate for the inhomogeneous approximation step.
The interval margin for the shift dominates the error in the homogeneous
approximation and the error in the candidate linear form. -/
theorem certificate_excludes (θ φ margin δ ε M : ℝ) (p q k : ℤ) (n : ℕ) (m : ℤ)
    (hq : 0 < q) (_hδ : 0 ≤ δ) (hn : (n : ℝ) ≤ M)
    (happrox : |(q : ℝ) * θ - p| ≤ δ)
    (hleft : (k : ℝ) + margin < (q : ℝ) * φ)
    (hright : (q : ℝ) * φ < (k : ℝ) + 1 - margin)
    (hmargin : M * δ + (q : ℝ) * ε ≤ margin) :
    ¬ |(n : ℝ) * θ - m + φ| ≤ ε := by
  intro hc
  let j : ℤ := n * p - m * q
  let s : ℝ := (n : ℝ) * ((q : ℝ) * θ - p)
  let L : ℝ := (n : ℝ) * θ - m + φ
  have hs : |s| ≤ M * δ := by
    change |(n : ℝ) * ((q : ℝ) * θ - p)| ≤ _
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ))]
    exact mul_le_mul hn happrox (abs_nonneg _) ((Nat.cast_nonneg n).trans hn)
  have hq' : 0 < (q : ℝ) := by exact_mod_cast hq
  have hL : |(q : ℝ) * L| ≤ (q : ℝ) * ε := by
    rw [abs_mul, abs_of_nonneg hq'.le]
    exact mul_le_mul_of_nonneg_left hc hq'.le
  have he : (j : ℝ) + (q : ℝ) * φ = (q : ℝ) * L - s := by
    simp only [j, L, s, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  have hj : |(j : ℝ) + (q : ℝ) * φ| ≤ margin := by
    rw [he]
    have htri := abs_sub ((q : ℝ) * L) s
    linarith
  obtain ⟨hl, hu⟩ := abs_le.mp hj
  by_cases hh : -j ≤ k
  · have hjk : -(j : ℝ) ≤ (k : ℝ) := by exact_mod_cast hh
    linarith
  · have hh' : k + 1 ≤ -j := by omega
    have hjk : (k : ℝ) + 1 ≤ -(j : ℝ) := by exact_mod_cast hh'
    linarith

/-- The single denominator 1641 works for both shifts, provided the stated
rational enclosures for the logarithmic ratios have been established. -/
theorem exclude_with_1641 (θ φ : ℝ) (n : ℕ) (m : ℤ) (hn : n ≤ 500)
    (hθ : (747105379 : ℝ) / 1000000000 ≤ θ ∧ θ ≤ 747105381 / 1000000000)
    (hφ : ((86803 : ℝ) / 1000000 ≤ φ ∧ φ ≤ 86805 / 1000000) ∨
      ((-493966 : ℝ) / 1000000 ≤ φ ∧ φ ≤ -493965 / 1000000)) :
    ¬ |(n : ℝ) * θ - m + φ| ≤ 1 / 10000 := by
  have happrox : |(1641 : ℝ) * θ - 1226| ≤ 1 / 10000 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hn' : (n : ℝ) ≤ 500 := by exact_mod_cast hn
  rcases hφ with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · apply certificate_excludes θ φ (1 / 4) (1 / 10000) (1 / 10000) 500
      1226 1641 142 n m (by decide) (by norm_num) hn' happrox
    · norm_num
      linarith
    · norm_num
      linarith
    · norm_num
  · apply certificate_excludes θ φ (1 / 4) (1 / 10000) (1 / 10000) 500
      1226 1641 (-811) n m (by decide) (by norm_num) hn' happrox
    · norm_num
      linarith
    · norm_num
      linarith
    · norm_num

#print axioms simultaneous_gap
#print axioms exclude_with_1641

end TupleLogGap
