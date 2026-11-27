import RatioCertificates
import TupleIndexDecay
import Mathlib.Tactic.IntervalCases

namespace TupleBDCertificates

/-- The normalized linear form is the index expression in the denominator certificates. -/
theorem normalize (n m : ℕ) (second : Bool) :
    TupleLogBridge.indexForm n m second / Real.log (3 + Real.sqrt 8) =
      (n : ℝ) * theta - (m : ℝ) + phi second := by
  have he : Real.log (3 + Real.sqrt 8) ≠ 0 :=
    (lt_trans (by norm_num) TupleIndexDecay.one_lt_log_unit).ne'
  simp only [TupleLogBridge.indexForm, theta, phi]
  field_simp

private theorem no_square_between (t v z : ℤ) (ht : 0 ≤ t) (hz : 0 < z)
    (hl : t * t < v) (hu : v < (t + 1) * (t + 1)) : z * z ≠ v := by
  intro he
  by_cases h : z ≤ t
  · have hzz : z * z ≤ t * t := Int.mul_le_mul h h hz.le ht
    omega
  · have h' : t + 1 ≤ z := by omega
    have hzz : (t + 1) * (t + 1) ≤ z * z := Int.mul_le_mul h' h' (by omega) hz.le
    omega

private theorem coord_eleven_of_index_le_five (n : ℕ) (x z : ℤ) (hn : n ≤ 5)
    (hx : 2 ≤ x) (hz : 0 < z) (horbit : (TuplePell.three n).1 = x)
    (he : z * z - 8 * x * x = -7) : x = 11 := by
  interval_cases n <;> norm_num [TuplePell.three] at horbit
  · omega
  · subst x
    exact (no_square_between 8 65 z (by decide) hz (by decide) (by decide)
      (by omega)).elim
  · omega
  · subst x
    exact (no_square_between 115 13441 z (by decide) hz (by decide) (by decide)
      (by omega)).elim
  · subst x
    exact (no_square_between 432 187265 z (by decide) hz (by decide) (by decide)
      (by omega)).elim
  · subst x
    exact (no_square_between 1615 2608321 z (by decide) hz (by decide) (by decide)
      (by omega)).elim

/-- If the first Pell orbit meets the index cutoff, the unique positive common
coordinate above one is eleven. The cutoff is the only analytic input left. -/
theorem coord_eleven_of_index_cutoff (x y z : ℤ) (hx : 2 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (he₃ : y * y - 3 * x * x = -2) (he₈ : z * z - 8 * x * x = -7)
    (hcutoff : ∀ n : ℕ, TuplePell.three n = (x, y) → n < 10 ^ 487) : x = 11 := by
  obtain ⟨n, m, second, hthree, _, hpos, hbound⟩ :=
    TupleLogBridge.index_form_bounds x y z hx hy hz he₃ he₈
  have hdecay := (TupleIndexDecay.normalized_error_bound n m second x y hthree hpos hbound).le
  rw [normalize] at hdecay
  have hdecay' : |(n : ℝ) * theta - ((m : ℤ) : ℝ) + phi second| ≤
      (5 : ℝ) / (24 * 4 ^ n) := by
    rw [Int.cast_natCast]
    calc
      _ ≤ (5 / 24 : ℝ) / 4 ^ n := hdecay
      _ = _ := by rw [div_div]
  have hn := index_le_five n (m : ℤ) second (hcutoff n hthree) hdecay'
  exact coord_eleven_of_index_le_five n x z hn hx hz (congrArg Prod.fst hthree) he₈

end TupleBDCertificates

#print axioms TupleBDCertificates.coord_eleven_of_index_cutoff
