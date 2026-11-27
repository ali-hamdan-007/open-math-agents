import Mathlib.Tactic.Linarith

namespace Graph199

/-- In a separator incidence matrix, total edges e and total ordered
row distances t constrain the number c of columns in terms of rows m. -/
theorem incidence_numbers {k m c e t : ℤ} (hk : 0 < k) (hm : 0 ≤ m)
    (he₁ : k*c ≤ e) (he₂ : e ≤ m*(k+1))
    (hs₁ : 2*k*c*m ≤ t + 2*k*e) (hs₂ : t ≤ k*m*(m-1)) :
    c ≤ m+1 := by
  by_contra! h
  have hlarge : m+2 ≤ c := by omega
  have hkm : 2*k ≤ m := by
    have h := mul_le_mul_of_nonneg_left hlarge hk.le
    nlinarith
  have hpos : 0 < k*m := mul_pos hk (by omega)
  have bound : k*m*(2*c) ≤ k*m*(m+2*k+1) := by
    have he := mul_le_mul_of_nonneg_left he₂ (show 0 ≤ 2*k by omega)
    nlinarith
  have hh : 2*c ≤ m+2*k+1 := (mul_le_mul_iff_right₀ hpos).mp bound
  omega

#print axioms incidence_numbers
end Graph199
