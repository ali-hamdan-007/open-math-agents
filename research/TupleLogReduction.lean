import TupleLogGap

namespace TupleLogReduction

private theorem decay_le (n N : ℕ) (hN : N ≤ n) :
    (5 : ℝ) / (24 * 4^n) ≤ 5 / (24 * 4^N) := by
  have hp : (4 : ℝ)^N ≤ 4^n := pow_le_pow_right₀ (by norm_num) hN
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr

set_option maxRecDepth 10000 in
set_option exponentiation.threshold 1000 in
/-- Two denominator certificates reduce an assumed bound of `10^487` to an
index at most five. The input also includes the normalized decay inequality
and the short rational intervals for the coefficient and the selected shift. -/
theorem two_stage_index_bound (θ φ : ℝ) (n : ℕ) (m p q k : ℤ)
    (hn : n < 10^487)
    (hdecay : |(n : ℝ) * θ - m + φ| ≤ (5 : ℝ) / (24 * 4^n))
    (hq : 0 < q) (hqmax : q ≤ 10^496)
    (hlargeApprox : |(q : ℝ) * θ - p| ≤ 1 / 10^488)
    (hlargeLeft : (k : ℝ) + 1 / 4 < (q : ℝ) * φ)
    (hlargeRight : (q : ℝ) * φ < (k : ℝ) + 1 - 1 / 4)
    (hθ : (747105379 : ℝ) / 1000000000 ≤ θ ∧ θ ≤ 747105381 / 1000000000)
    (hφ : ((86803 : ℝ) / 1000000 ≤ φ ∧ φ ≤ 86805 / 1000000) ∨
      ((-493966 : ℝ) / 1000000 ≤ φ ∧ φ ≤ -493965 / 1000000)) :
    n ≤ 5 := by
  have hn' : (n : ℝ) ≤ 10^487 := by exact_mod_cast hn.le
  have hqmax' : (q : ℝ) ≤ 10^496 := by exact_mod_cast hqmax
  have hfirst : n < 850 := by
    by_contra! hb
    have hceil : (5 : ℝ) / (24 * 4^850) ≤ 1 / 10^497 := by norm_num
    have hsmall := hdecay.trans ((decay_le n 850 hb).trans hceil)
    have hmargin : (10 : ℝ)^487 * (1 / 10^488) + (q : ℝ) * (1 / 10^497) ≤ 1 / 4 := by
      calc
        _ ≤ (10 : ℝ)^487 * (1 / 10^488) + (10 : ℝ)^496 * (1 / 10^497) :=
          add_le_add_right (mul_le_mul_of_nonneg_right hqmax' (by norm_num : (0 : ℝ) ≤ 1 / 10^497)) _
        _ ≤ _ := by norm_num
    exact TupleLogGap.certificate_excludes θ φ (1 / 4) (1 / 10^488) (1 / 10^497)
      (10^487) p q k n m hq (by positivity) hn' hlargeApprox hlargeLeft hlargeRight hmargin hsmall
  by_contra! hfinal
  have hceil : (5 : ℝ) / (24 * 4^6) ≤ 1 / 10000 := by norm_num
  have hsmall := hdecay.trans ((decay_le n 6 hfinal).trans hceil)
  have hshortApprox : |(1641 : ℝ) * θ - 1226| ≤ 1 / 10000 := by
    rw [abs_le]
    constructor <;> linarith [hθ.1, hθ.2]
  have hn'' : (n : ℝ) ≤ 850 := by exact_mod_cast hfirst.le
  rcases hφ with ⟨hl, hu⟩ | ⟨hl, hu⟩
  · refine TupleLogGap.certificate_excludes θ φ (1 / 4) (1 / 10000) (1 / 10000)
      850 1226 1641 142 n m (by decide) (by norm_num) hn'' hshortApprox ?_ ?_ ?_ hsmall
    · norm_num
      linarith
    · norm_num
      linarith
    · norm_num
  · refine TupleLogGap.certificate_excludes θ φ (1 / 4) (1 / 10000) (1 / 10000)
      850 1226 1641 (-811) n m (by decide) (by norm_num) hn'' hshortApprox ?_ ?_ ?_ hsmall
    · norm_num
      linarith
    · norm_num
      linarith
    · norm_num

#print axioms two_stage_index_bound

end TupleLogReduction
