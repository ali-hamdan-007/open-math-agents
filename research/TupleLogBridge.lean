import TuplePell
import TupleLogGap

namespace TupleLogBridge

private theorem pell_step (D u x y : ℝ) (hD : 0 < D) :
    (u*x+y) + (D*x+u*y) / Real.sqrt D =
      (x + y / Real.sqrt D) * (u + Real.sqrt D) := by
  have hs : Real.sqrt D ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD.le
  field_simp [hs]
  nlinarith [congrArg (fun t => t * x) hsq]

/-- The normalized factor of the orbit for `y² - 3x² = -2`. -/
theorem three_closed (n : ℕ) :
    ((TuplePell.three n).1 : ℝ) + ((TuplePell.three n).2 : ℝ) / Real.sqrt 3 =
      (1 + 1 / Real.sqrt 3) * (2 + Real.sqrt 3) ^ n := by
  induction n with
  | zero => simp [TuplePell.three]
  | succ n ih =>
    cases he : TuplePell.three n with
    | mk x y =>
      simp only [he, Int.cast_mul, Int.cast_add, Int.cast_ofNat, TuplePell.three] at ih ⊢
      rw [pell_step 3 2 (x : ℝ) (y : ℝ) (by norm_num), ih, pow_succ, mul_assoc]

/-- The seed of the normalized factor of either orbit for `z² - 8x² = -7`. -/
noncomputable def eightSeed (second : Bool) : ℝ :=
  if second then 2 + 5 / Real.sqrt 8 else 1 + 1 / Real.sqrt 8

/-- The normalized factor of either orbit for `z² - 8x² = -7`. -/
theorem eight_closed (second : Bool) (n : ℕ) :
    ((TuplePell.eight second n).1 : ℝ) + ((TuplePell.eight second n).2 : ℝ) / Real.sqrt 8 =
      eightSeed second * (3 + Real.sqrt 8) ^ n := by
  induction n with
  | zero => cases second <;> simp [TuplePell.eight, eightSeed]
  | succ n ih =>
    cases he : TuplePell.eight second n with
    | mk x z =>
      simp only [he, Int.cast_mul, Int.cast_add, Int.cast_ofNat, TuplePell.eight] at ih ⊢
      rw [pell_step 8 3 (x : ℝ) (z : ℝ) (by norm_num), ih, pow_succ, mul_assoc]

/-- The logarithmic form in the two orbit indices. -/
noncomputable def indexForm (n m : ℕ) (second : Bool) : ℝ :=
  (n : ℝ) * Real.log (2 + Real.sqrt 3) - (m : ℝ) * Real.log (3 + Real.sqrt 8) +
    Real.log ((1 + 1 / Real.sqrt 3) / eightSeed second)

/-- At a shared first coordinate, the logarithmic quotient is the index form. -/
theorem gap_eq_form (x y z : ℤ) (n m : ℕ) (second : Bool)
    (h₃ : TuplePell.three n = (x,y)) (h₈ : TuplePell.eight second m = (x,z)) :
    Real.log (((x : ℝ) + (y : ℝ) / Real.sqrt 3) / ((x : ℝ) + (z : ℝ) / Real.sqrt 8)) =
      indexForm n m second := by
  have ha : 0 < (1 : ℝ) + 1 / Real.sqrt 3 := by positivity
  have hb : 0 < eightSeed second := by cases second <;> simp [eightSeed] <;> positivity
  have hu : 0 < (2 : ℝ) + Real.sqrt 3 := by positivity
  have hv : 0 < (3 : ℝ) + Real.sqrt 8 := by positivity
  have hleft := three_closed n
  have hright := eight_closed second m
  rw [h₃] at hleft
  rw [h₈] at hright
  rw [hleft, hright, Real.log_div (mul_pos ha (pow_pos hu n)).ne'
    (mul_pos hb (pow_pos hv m)).ne',
    Real.log_mul ha.ne' (pow_pos hu n).ne',
    Real.log_mul hb.ne' (pow_pos hv m).ne', Real.log_pow, Real.log_pow]
  unfold indexForm
  rw [Real.log_div ha.ne' hb.ne']
  ring

/-- Every positive simultaneous Pell solution with `x ≥ 2` gives a nonzero
linear form in the two recurrence indices, with an explicit upper bound. -/
theorem index_form_bounds (x y z : ℤ) (hx : 2 ≤ x) (hy : 0 < y) (hz : 0 < z)
    (he₃ : y*y - 3*x*x = -2) (he₈ : z*z - 8*x*x = -7) :
    ∃ n m second,
      TuplePell.three n = (x,y) ∧ TuplePell.eight second m = (x,z) ∧
      0 < indexForm n m second ∧ indexForm n m second < (5 / 24) / (x : ℝ) ^ 2 := by
  obtain ⟨n, hn⟩ := TuplePell.three_complete x y (by omega) hy he₃
  obtain ⟨second, m, hm⟩ := TuplePell.eight_complete x z (by omega) hz he₈
  have he₃' : (y : ℝ)^2 = 3 * (x : ℝ)^2 - 2 := by
    exact_mod_cast (show y^2 = 3*x^2 - 2 by grind)
  have he₈' : (z : ℝ)^2 = 8 * (x : ℝ)^2 - 7 := by
    exact_mod_cast (show z^2 = 8*x^2 - 7 by grind)
  have hgap := TupleLogGap.simultaneous_gap (x : ℝ) (y : ℝ) (z : ℝ)
    (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hz) he₃' he₈'
  dsimp only at hgap
  rw [gap_eq_form x y z n m second hn hm] at hgap
  exact ⟨n, m, second, hn, hm, hgap⟩

#print axioms index_form_bounds

end TupleLogBridge
