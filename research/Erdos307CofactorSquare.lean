import Erdos307CrossCoprime
import Mathlib.Data.ZMod.Basic

namespace Erdos307Structure

open Finset
open scoped BigOperators

private theorem dvd_member_denom {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∣ denom A := by
  refine ⟨denom (A.erase a), ?_⟩
  simpa [denom, mul_comm] using (Finset.prod_erase_mul A id ha).symm

private theorem cofactor_eq_erased_product {A : Finset ℕ} {a : ℕ}
    (ha : a ∈ A) (ha0 : 0 < a) : denom A / a = denom (A.erase a) := by
  have he : denom (A.erase a) * a = denom A := Finset.prod_erase_mul A id ha
  rw [← he, Nat.mul_div_cancel _ ha0]

/-- A cross-product equality makes the full support cofactor congruent
to the other side's product squared, modulo the selected denominator.
This applies to composite denominators as well as primes. -/
theorem product_cofactor_eq_square_mod_member {A B : Finset ℕ} {p : ℕ}
    (hp : p ∈ A) (hA : ∀ a ∈ A, 0 < a) (hswap : numer A = denom B) :
    (((denom A * denom B) / p : ℕ) : ZMod p) = (denom B : ZMod p) ^ 2 := by
  have hs : (∑ a ∈ A.erase p, ((denom A / a : ℕ) : ZMod p)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have ha' := Finset.mem_of_mem_erase ha
    rw [cofactor_eq_erased_product ha' (hA a ha'), ZMod.natCast_eq_zero_iff]
    apply dvd_member_denom
    exact Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase ha).symm, hp⟩
  have hco : (numer A : ZMod p) = ((denom A / p : ℕ) : ZMod p) := by
    rw [numer, Nat.cast_sum, ← Finset.sum_erase_add _ _ hp, hs, zero_add]
  rw [hswap] at hco
  rw [mul_comm (denom A), Nat.mul_div_assoc _ (dvd_member_denom hp), Nat.cast_mul,
    ← hco, pow_two]

/-- Every denominator in a reciprocal-product solution has square support
cofactor modulo itself. This statement is independent of the partition. -/
theorem support_cofactor_isSquare_of_reciprocals {P Q : Finset ℕ} {p : ℕ}
    (hP : ∀ a ∈ P, 1 < a) (hQ : ∀ b ∈ Q, 1 < b)
    (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (hmul : 1 = (∑ a ∈ P, (a : ℚ)⁻¹) * (∑ b ∈ Q, (b : ℚ)⁻¹))
    (hp : p ∈ P ∪ Q) : IsSquare (((denom (P ∪ Q) / p : ℕ) : ZMod p)) := by
  have hp0 (a : ℕ) (ha : a ∈ P) : 0 < a := Nat.zero_lt_of_lt (hP a ha)
  have hq0 (b : ℕ) (hb : b ∈ Q) : 0 < b := Nat.zero_lt_of_lt (hQ b hb)
  obtain ⟨hPQ, hQP, hcross⟩ := swap_products P Q hp0 hq0 hpw hqw hmul
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h := hcross a ha a hb
    rw [Nat.Coprime, Nat.gcd_self] at h
    exact (Nat.ne_of_gt (hP a ha)) h
  have hprod : denom (P ∪ Q) = denom P * denom Q := Finset.prod_union hdis
  rw [hprod]
  rcases Finset.mem_union.mp hp with ha | hb
  · exact ⟨(denom Q : ZMod p), by
      simpa only [pow_two] using product_cofactor_eq_square_mod_member ha hp0 hPQ⟩
  · exact ⟨(denom P : ZMod p), by
      simpa only [pow_two, mul_comm (denom Q)] using
        product_cofactor_eq_square_mod_member hb hq0 hQP⟩

#print axioms product_cofactor_eq_square_mod_member
#print axioms support_cofactor_isSquare_of_reciprocals

end Erdos307Structure
