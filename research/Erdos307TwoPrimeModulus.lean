import Erdos307CrossCoprime
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination

namespace Erdos307Structure

private theorem square_of_scaled_squares {m : ℕ} {A B a b : ZMod m}
    (ha : IsUnit a) (h : A * b ^ 2 = B * a ^ 2) : IsSquare (A * B) := by
  obtain ⟨u, hu⟩ := ha
  let v : ZMod m := ↑u⁻¹
  have huv : (u : ZMod m) * v = 1 := by simp [v]
  have hh : A * b ^ 2 = B * (u : ZMod m) ^ 2 := by rwa [hu]
  refine ⟨A * b * v, ?_⟩
  calc
    A * B = (A * B) * ((u : ZMod m) * v) ^ 2 := by rw [huv]; simp
    _ = A * (B * (u : ZMod m) ^ 2) * v ^ 2 := by ring
    _ = A * (A * b ^ 2) * v ^ 2 := by rw [← hh]
    _ = (A * b * v) * (A * b * v) := by ring

private theorem pair_product_neg_square {m a b : ℕ} (hs : m ∣ a + b) :
    (a : ZMod m) * b = - (a : ZMod m) ^ 2 := by
  have h := (ZMod.natCast_eq_zero_iff (a + b) m).mpr hs
  rw [Nat.cast_add] at h
  have hb : (b : ZMod m) = -(a : ZMod m) := by linear_combination h
  rw [hb]
  ring

/-- In a two-by-two closing frame, every divisor m of both closing sums
forces the crossed base-product/cofactor pairs to be squares modulo m.
This applies without requiring the two closing sums to be equal. -/
theorem square_cross_products_of_two_slots {M U N V a b c d m : ℕ}
    (hab : a.Coprime b) (hcd : c.Coprime d)
    (hsL : m ∣ a + b) (hsR : m ∣ c + d)
    (hL : N * (c * d) = U * (a * b) + M * (a + b))
    (hR : M * (a * b) = V * (c * d) + N * (c + d)) :
    IsSquare ((N : ZMod m) * U) ∧ IsSquare ((M : ZMod m) * V) := by
  have ha : a.Coprime m := (Nat.coprime_self_add_right.mpr hab).coprime_dvd_right hsL
  have hc : c.Coprime m := (Nat.coprime_self_add_right.mpr hcd).coprime_dvd_right hsR
  have hua : IsUnit (a : ZMod m) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime a ha).isUnit
  have huc : IsUnit (c : ZMod m) := by
    simpa only [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime c hc).isUnit
  have hsumL := (ZMod.natCast_eq_zero_iff (a + b) m).mpr hsL
  have hsumR := (ZMod.natCast_eq_zero_iff (c + d) m).mpr hsR
  rw [Nat.cast_add] at hsumL hsumR
  have hl := congrArg (fun n : ℕ => (n : ZMod m)) hL
  have hr := congrArg (fun n : ℕ => (n : ZMod m)) hR
  simp only [Nat.cast_mul, Nat.cast_add, hsumL, hsumR, pair_product_neg_square hsL,
    pair_product_neg_square hsR, mul_zero, add_zero, mul_neg] at hl hr
  exact ⟨square_of_scaled_squares hua (neg_injective hl),
    square_of_scaled_squares huc (neg_injective hr)⟩

/-- An explicit infinite obstruction for two-by-two constructions: both sums
cannot be multiples of 3 when either crossed base product is 2 modulo 3. -/
theorem no_two_slots_of_cross_product_mod_three {M U N V a b c d : ℕ}
    (hab : a.Coprime b) (hcd : c.Coprime d)
    (hsL : 3 ∣ a + b) (hsR : 3 ∣ c + d)
    (hL : N * (c * d) = U * (a * b) + M * (a + b))
    (hR : M * (a * b) = V * (c * d) + N * (c + d))
    (hbad : (N * U) % 3 = 2 ∨ (M * V) % 3 = 2) : False := by
  have hsq := square_cross_products_of_two_slots hab hcd hsL hsR hL hR
  have hno : ¬ IsSquare (2 : ZMod 3) := by
    rintro ⟨x, hx⟩
    fin_cases x <;> exact (by decide : (2 : ZMod 3) ≠ _) hx
  rcases hbad with h | h
  · apply hno
    have he : ((N : ZMod 3) * U) = 2 := by
      rw [← Nat.cast_mul, ← ZMod.natCast_mod (N * U) 3, h]
      rfl
    exact he ▸ hsq.1
  · apply hno
    have he : ((M : ZMod 3) * V) = 2 := by
      rw [← Nat.cast_mul, ← ZMod.natCast_mod (M * V) 3, h]
      rfl
    exact he ▸ hsq.2

#print axioms square_cross_products_of_two_slots
#print axioms no_two_slots_of_cross_product_mod_three
end Erdos307Structure
