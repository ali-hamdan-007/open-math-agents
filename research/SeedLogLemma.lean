import RationalLogBounds
import Mathlib.Analysis.Real.Sqrt

namespace SeedLogLemma

private theorem sqrtEnclosure {d D r : ℕ} (hD : 0 < D)
    (hlo : r ^ 2 ≤ d * D ^ 2) (hhi : d * D ^ 2 ≤ (r + 1) ^ 2) :
    (r : ℝ) / D ≤ Real.sqrt d ∧ Real.sqrt d ≤ (r + 1 : ℝ) / D := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  constructor
  · apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast hlo
  · apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast hhi

/-- Fixed-point certificate for the log of an affine function of a reciprocal square root. -/
theorem reciprocalSqrt {d u v r p q D n : ℕ}
    (hD : 0 < D) (hn : 0 < n) (hp : p ≤ D) (hu : 0 < u) (hr : 0 < r)
    (hroot₁ : r ^ 2 ≤ d * D ^ 2) (hroot₂ : d * D ^ 2 ≤ (r + 1) ^ 2)
    (hlo : RationalLogBounds.fixedUpper p D n ^ 2 ≤
      (u : ℚ) + (v : ℚ) / (((r : ℚ) + 1) / D))
    (hhi : (u : ℚ) + (v : ℚ) / ((r : ℚ) / D) ≤
      RationalLogBounds.fixedLower q D n ^ 2) :
    2 * ((p : ℝ) / D) ≤ Real.log ((u : ℝ) + (v : ℝ) / Real.sqrt d) ∧
    Real.log ((u : ℝ) + (v : ℝ) / Real.sqrt d) ≤ 2 * ((q : ℝ) / D) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hroot := sqrtEnclosure hD hroot₁ hroot₂
  have hsqrt : 0 < Real.sqrt (d : ℝ) := (div_pos hr' hD').trans_le hroot.1
  have hlo' : (0 : ℚ) < (u : ℚ) + (v : ℚ) / (((r : ℚ) + 1) / D) :=
    add_pos_of_pos_of_nonneg huq (by positivity)
  have hx₁ : (((u : ℚ) + (v : ℚ) / (((r : ℚ) + 1) / D) : ℚ) : ℝ) ≤
      (u : ℝ) + (v : ℝ) / Real.sqrt d := by
    push_cast
    exact add_le_add_right (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (v : ℝ) by positivity) hsqrt hroot.2) _
  have hx₂ : (u : ℝ) + (v : ℝ) / Real.sqrt d ≤
      (((u : ℚ) + (v : ℚ) / ((r : ℚ) / D) : ℚ) : ℝ) := by
    push_cast
    exact add_le_add_right (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (v : ℝ) by positivity) (div_pos hr' hD') hroot.1) _
  simpa only [Nat.cast_ofNat] using
    RationalLogBounds.fixedEnclosure 2 hD hn hp hlo' hx₁ hx₂ hlo hhi

end SeedLogLemma

#print axioms SeedLogLemma.reciprocalSqrt
