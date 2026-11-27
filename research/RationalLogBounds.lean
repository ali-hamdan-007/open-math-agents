import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Rational certificates for real logarithms

Bound the exponential at rational endpoints, then use its monotonic inverse.
Scaling the endpoint by a natural number allows the exponential bounds to use
only arguments between zero and one. All certificate inequalities are rational.
-/

open scoped BigOperators

namespace RationalLogBounds

/-- Rational truncation of the exponential series. -/
def expLower (x : ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℚ)

/-- The same truncation with Mathlib's factorially decaying error bound. -/
def expUpper (x : ℚ) (n : ℕ) : ℚ :=
  expLower x n + x ^ n * ((n : ℚ) + 1) / ((n.factorial : ℚ) * n)

theorem expLower_le_exp {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (expLower x n : ℝ) ≤ Real.exp (x : ℝ) := by
  have hx' : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  simpa only [expLower, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    using Real.sum_le_exp_of_nonneg hx' n

theorem exp_le_expUpper {x : ℚ} (hx : 0 ≤ x) (hx' : x ≤ 1) {n : ℕ} (hn : 0 < n) :
    Real.exp (x : ℝ) ≤ (expUpper x n : ℝ) := by
  have h₀ : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h₁ : (x : ℝ) ≤ 1 := by exact_mod_cast hx'
  simpa only [expUpper, expLower, Rat.cast_sum, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_natCast, Rat.cast_one] using Real.exp_bound' h₀ h₁ hn

theorem expLower_nonneg {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ expLower x n := by
  unfold expLower
  exact Finset.sum_nonneg fun i _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)

/-- Certify a real logarithm from rational bounds on its positive argument.
A scale of 2 is sufficient for candidates below 2, for example. -/
theorem enclosure {x : ℝ} {a b lo hi : ℚ} {n : ℕ} (scale : ℕ)
    (ha : 0 < a) (hx₁ : (a : ℝ) ≤ x) (hx₂ : x ≤ (b : ℝ)) (hn : 0 < n)
    (hlo₀ : 0 ≤ lo) (hlo₁ : lo ≤ 1) (hhi₀ : 0 ≤ hi)
    (hlo : expUpper lo n ^ scale ≤ a) (hhi : b ≤ expLower hi n ^ scale) :
    (scale : ℝ) * (lo : ℝ) ≤ Real.log x ∧ Real.log x ≤ (scale : ℝ) * (hi : ℝ) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hx : 0 < x := ha'.trans_le hx₁
  have hlo' : (expUpper lo n : ℝ) ^ scale ≤ (a : ℝ) := by exact_mod_cast hlo
  have hhi' : (b : ℝ) ≤ (expLower hi n : ℝ) ^ scale := by exact_mod_cast hhi
  have hUpperNonneg : (0 : ℝ) ≤ (expUpper lo n : ℝ) :=
    (Real.exp_pos _).le.trans (exp_le_expUpper hlo₀ hlo₁ hn)
  have hLowerNonneg : (0 : ℝ) ≤ (expLower hi n : ℝ) := by
    exact_mod_cast expLower_nonneg hhi₀ n
  constructor
  · apply (Real.le_log_iff_exp_le hx).mpr
    rw [Real.exp_nat_mul]
    exact (pow_le_pow_left₀ (Real.exp_pos _).le (exp_le_expUpper hlo₀ hlo₁ hn) scale).trans
      (hlo'.trans hx₁)
  · apply (Real.log_le_iff_le_exp hx).mpr
    rw [Real.exp_nat_mul]
    exact hx₂.trans (hhi'.trans
      (pow_le_pow_left₀ hLowerNonneg (expLower_le_exp hhi₀ n) scale))


/-- Fixed-point term and accumulated sum for the first `n` terms of
`exp (p / D)`. Each term is rounded down or up in units of `1 / D`. -/
def fixed (p D : ℕ) (upper : Bool) : ℕ → ℕ × ℕ
  | 0 => (D, 0)
  | n + 1 =>
    let (term, total) := fixed p D upper n
    let next := term * p / (D * (n + 1))
    (if upper then next + 1 else next, total + term)

private def term (p D n : ℕ) : ℚ := ((p : ℚ) / D) ^ n / n.factorial

private theorem term_succ (p D n : ℕ) (hD : 0 < D) :
    term p D (n + 1) = term p D n * ((p : ℚ) / D) / (n + 1 : ℕ) := by
  unfold term
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul]
  have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hn' : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

private theorem step_floor (p D n t : ℕ) (hD : 0 < D) :
    ((t * p / (D * (n + 1)) : ℕ) : ℚ) / D ≤
      ((t : ℚ) / D) * ((p : ℚ) / D) / (n + 1 : ℕ) := by
  have hM : (0 : ℚ) < (D : ℚ) * ((n + 1 : ℕ) : ℚ) := by positivity
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have h := Nat.div_mul_le_self (t * p) (D * (n + 1))
  have h' : ((t * p / (D * (n + 1)) : ℕ) : ℚ) * ((D : ℚ) * (n + 1 : ℕ)) ≤
      (t : ℚ) * p := by exact_mod_cast h
  have eh : ((t : ℚ) / D) * ((p : ℚ) / D) / (n + 1 : ℕ) =
      ((t : ℚ) * p / ((D : ℚ) * (n + 1 : ℕ))) / D := by
    field_simp
  rw [eh]
  exact div_le_div_of_nonneg_right ((le_div_iff₀ hM).mpr h') hD'.le

private theorem step_ceil (p D n t : ℕ) (hD : 0 < D) :
    ((t : ℚ) / D) * ((p : ℚ) / D) / (n + 1 : ℕ) ≤
      ((t * p / (D * (n + 1)) + 1 : ℕ) : ℚ) / D := by
  have hM : (0 : ℚ) < (D : ℚ) * ((n + 1 : ℕ) : ℚ) := by positivity
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hM' : 0 < D * (n + 1) := Nat.mul_pos hD (Nat.succ_pos _)
  have h := (Nat.div_lt_iff_lt_mul hM').mp (Nat.lt_succ_self (t * p / (D * (n + 1))))
  have h' : (t : ℚ) * p ≤
      ((t * p / (D * (n + 1)) + 1 : ℕ) : ℚ) * ((D : ℚ) * (n + 1 : ℕ)) :=
    by exact_mod_cast h.le
  have eh : ((t : ℚ) / D) * ((p : ℚ) / D) / (n + 1 : ℕ) =
      ((t : ℚ) * p / ((D : ℚ) * (n + 1 : ℕ))) / D := by
    field_simp
  rw [eh]
  exact div_le_div_of_nonneg_right ((div_le_iff₀ hM).mpr h') hD'.le

private theorem fixed_bounds (p D n : ℕ) (hD : 0 < D) :
    ((fixed p D false n).1 : ℚ) / D ≤ term p D n ∧
    term p D n ≤ ((fixed p D true n).1 : ℚ) / D ∧
    ((fixed p D false n).2 : ℚ) / D ≤ expLower ((p : ℚ) / D) n ∧
    expLower ((p : ℚ) / D) n ≤ ((fixed p D true n).2 : ℚ) / D := by
  induction n with
  | zero =>
    have hD' : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    simp [fixed, term, expLower, hD']
  | succ n ih =>
    obtain ⟨ht₁, ht₂, hs₁, hs₂⟩ := ih
    have hr : 0 ≤ (p : ℚ) / D := by positivity
    have hn : (0 : ℚ) ≤ (n + 1 : ℕ) := by positivity
    simp only [fixed, Bool.false_eq_true, if_false, if_true]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [term_succ _ _ _ hD]
      exact (step_floor _ _ _ _ hD).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht₁ hr) hn)
    · rw [term_succ _ _ _ hD]
      exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht₂ hr) hn).trans
        (step_ceil _ _ _ _ hD)
    · rw [Nat.cast_add, add_div]
      simpa only [expLower, Finset.sum_range_succ, term] using add_le_add hs₁ ht₁
    · rw [Nat.cast_add, add_div]
      simpa only [expLower, Finset.sum_range_succ, term] using add_le_add hs₂ ht₂

/-- A computable fixed-point lower bound for the exponential. -/
def fixedLower (p D n : ℕ) : ℚ := ((fixed p D false n).2 : ℚ) / D

/-- A computable fixed-point upper bound for the exponential, including its tail. -/
def fixedUpper (p D n : ℕ) : ℚ :=
  (((fixed p D true n).2 + 2 * (fixed p D true n).1 : ℕ) : ℚ) / D

theorem fixedLower_le_expLower (p D n : ℕ) (hD : 0 < D) :
    fixedLower p D n ≤ expLower ((p : ℚ) / D) n :=
  (fixed_bounds p D n hD).2.2.1

theorem expUpper_le_fixedUpper (p D n : ℕ) (hD : 0 < D) (hn : 0 < n) :
    expUpper ((p : ℚ) / D) n ≤ fixedUpper p D n := by
  obtain ⟨_, ht, _, hs⟩ := fixed_bounds p D n hD
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hone : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hratio : ((n : ℚ) + 1) / n ≤ 2 := (div_le_iff₀ hn').mpr (by linarith)
  have hnonneg : 0 ≤ term p D n := by unfold term; positivity
  have htail : ((p : ℚ) / D) ^ n * ((n : ℚ) + 1) / ((n.factorial : ℚ) * n) =
      term p D n * (((n : ℚ) + 1) / n) := by rw [term, div_mul_div_comm]
  rw [expUpper, htail]
  calc
    _ ≤ ((fixed p D true n).2 : ℚ) / D + 2 * (((fixed p D true n).1 : ℚ) / D) :=
      add_le_add hs ((mul_le_mul_of_nonneg_left hratio hnonneg).trans (by linarith))
    _ = fixedUpper p D n := by
      unfold fixedUpper
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, add_div, mul_div_assoc]

/-- A fixed-point certificate for logarithms. The two certificate inequalities
can be checked using integer arithmetic on numbers with only a few more digits
than the requested precision. -/
theorem fixedEnclosure {x : ℝ} {a b : ℚ} {p q D n : ℕ} (scale : ℕ)
    (hD : 0 < D) (hn : 0 < n) (hp : p ≤ D)
    (ha : 0 < a) (hx₁ : (a : ℝ) ≤ x) (hx₂ : x ≤ (b : ℝ))
    (hlo : fixedUpper p D n ^ scale ≤ a)
    (hhi : b ≤ fixedLower q D n ^ scale) :
    (scale : ℝ) * ((p : ℝ) / D) ≤ Real.log x ∧
      Real.log x ≤ (scale : ℝ) * ((q : ℝ) / D) := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hp' : ((p : ℚ) / D) ≤ 1 := (div_le_one hD').mpr (by exact_mod_cast hp)
  have hlo' : expUpper ((p : ℚ) / D) n ^ scale ≤ a := by
    refine (pow_le_pow_left₀ ?_ (expUpper_le_fixedUpper p D n hD hn) scale).trans hlo
    unfold expUpper
    exact add_nonneg (expLower_nonneg (by positivity) _) (by positivity)
  have hhi' : b ≤ expLower ((q : ℚ) / D) n ^ scale :=
    hhi.trans (pow_le_pow_left₀ (by unfold fixedLower; positivity)
      (fixedLower_le_expLower q D n hD) scale)
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    enclosure scale ha hx₁ hx₂ hn (by positivity) hp' (by positivity) hlo' hhi'

end RationalLogBounds

#print axioms RationalLogBounds.enclosure
#print axioms RationalLogBounds.fixedEnclosure
