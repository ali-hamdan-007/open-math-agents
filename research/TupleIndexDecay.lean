import TupleLogBridge

namespace TupleIndexDecay

/-- The first Pell coordinate at least doubles with every recurrence step. -/
theorem three_growth (n : ℕ) :
    (2 : ℤ) ^ n ≤ (TuplePell.three n).1 ∧ 0 < (TuplePell.three n).2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    cases hp : TuplePell.three n with
    | mk x y =>
      simp only [hp] at ih
      simp only [TuplePell.three, hp, pow_succ]
      have hpos : (0 : ℤ) < 2 ^ n := by positivity
      omega

theorem one_lt_log_unit : 1 < Real.log (3 + Real.sqrt 8) := by
  have h := Real.lt_log_one_add_of_pos (x := 2) (by norm_num)
  norm_num at h
  exact h.trans_le (Real.log_le_log (by norm_num) (by linarith [Real.sqrt_nonneg 8]))

/-- The normalized error is controlled by the first Pell index alone. -/
theorem normalized_error_bound (n m : ℕ) (second : Bool) (x y : ℤ)
    (horbit : TuplePell.three n = (x,y))
    (hpos : 0 < TupleLogBridge.indexForm n m second)
    (hbound : TupleLogBridge.indexForm n m second < (5 / 24) / (x : ℝ) ^ 2) :
    |TupleLogBridge.indexForm n m second / Real.log (3 + Real.sqrt 8)| <
      (5 / 24) / (4 : ℝ) ^ n := by
  have hx := (three_growth n).1
  rw [horbit] at hx
  have hx' : (2 : ℝ)^n ≤ (x : ℝ) := by exact_mod_cast hx
  have ht : (0 : ℝ) < 2 ^ n := by positivity
  have hsq : (4 : ℝ)^n ≤ (x : ℝ)^2 := by
    calc
      (4 : ℝ)^n = ((2 : ℝ)^n)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hx') (add_nonneg (ht.le.trans hx') ht.le)]
  have hlog := one_lt_log_unit
  rw [abs_of_pos (div_pos hpos (by linarith))]
  calc
    _ ≤ TupleLogBridge.indexForm n m second := div_le_self hpos.le hlog.le
    _ < _ := hbound
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq

#print axioms normalized_error_bound

end TupleIndexDecay
