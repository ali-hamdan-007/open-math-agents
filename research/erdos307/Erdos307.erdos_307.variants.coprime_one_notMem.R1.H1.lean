import OMAReductions.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum

open Finset
open scoped BigOperators

theorem OMA.solution : OMA.R_Erdos307_erdos_307_variants_coprime_one_notMem_R1.H1 := by
  intro A hA
  have dvd_product (a : ℕ) (ha : a ∈ A) : a ∣ ∏ x ∈ A, x := by
    exact ⟨∏ x ∈ A.erase a, x, (Finset.mul_prod_erase A (fun x => x) ha).symm⟩
  constructor
  · rw [Finset.mul_sum, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hane : (a : ℚ) ≠ 0 := by exact_mod_cast (hA a ha).ne'
    rw [← Nat.cast_prod, ← div_eq_mul_inv]
    apply (div_eq_iff hane).2
    exact_mod_cast (Nat.div_mul_cancel (dvd_product a ha)).symm
  · intro w hw hwA
    rw [Finset.sum_insert hwA, Finset.prod_insert hwA,
      Nat.mul_div_cancel_left _ hw, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun a ha => Nat.mul_div_assoc w (dvd_product a ha)

