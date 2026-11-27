import Erdos307CrossCoprime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos307Structure
open Finset
open scoped BigOperators

private theorem dvd_group_product {A : Finset ℕ} {a : ℕ} (ha : a ∈ A) :
    a ∣ denom A := by
  refine ⟨denom (A.erase a), ?_⟩
  simpa [denom, mul_comm] using (Finset.prod_erase_mul A id ha).symm

private theorem clear_group_reciprocals {A : Finset ℕ} (hA : ∀ a ∈ A, 0 < a) :
    (denom A : ℚ) * (∑ a ∈ A, (1 : ℚ) / a) = numer A := by
  rw [numer, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hz : (a : ℚ) ≠ 0 := by exact_mod_cast (hA a ha).ne'
  rw [mul_one_div]
  apply (div_eq_iff hz).mpr
  exact_mod_cast (Nat.div_mul_cancel (dvd_group_product ha)).symm

private theorem denom_eq_of_sum_eq {A B : Finset ℕ}
    (ha : ∀ a ∈ A, 0 < a) (hb : ∀ b ∈ B, 0 < b)
    (hA : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hB : Set.Pairwise (B : Set ℕ) Nat.Coprime)
    (hs : (∑ a ∈ A, (1 : ℚ) / a) = ∑ b ∈ B, (1 : ℚ) / b) :
    denom A = denom B := by
  have hcross : numer A * denom B = numer B * denom A := by
    exact_mod_cast (show (numer A : ℚ) * (denom B : ℚ) =
      (numer B : ℚ) * (denom A : ℚ) by
        rw [← clear_group_reciprocals ha, ← clear_group_reciprocals hb, hs]
        ring)
  exact Nat.dvd_antisymm
    ((reduced_cofactor_sum A ha hA).symm.dvd_of_dvd_mul_left
      (hcross.symm ▸ dvd_mul_left (denom A) (numer B)))
    ((reduced_cofactor_sum B hb hB).symm.dvd_of_dvd_mul_left
      (hcross ▸ dvd_mul_left (denom B) (numer A)))

private theorem mem_prime_group_of_dvd {B : Finset ℕ} (hB : ∀ b ∈ B, Nat.Prime b)
    {p : ℕ} (hp : Nat.Prime p) (hd : p ∣ denom B) : p ∈ B := by
  have hh := (hp.prime.dvd_finsetProd_iff (S := B) id).mp hd
  obtain ⟨b, hb, hpb⟩ := hh
  obtain h | h := (Nat.dvd_prime (hB b hb)).mp hpb
  · exact (hp.ne_one h).elim
  · exact h ▸ hb

private theorem minFac_inj {A : Finset ℕ} (hA : ∀ a ∈ A, 1 < a)
    (hcp : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    Set.InjOn Nat.minFac (A : Set ℕ) := by
  intro a ha b hb he
  by_contra hn
  have hg := Nat.dvd_gcd (Nat.minFac_dvd a) (he ▸ Nat.minFac_dvd b)
  rw [hcp ha hb hn] at hg
  exact (Nat.minFac_prime (Nat.ne_of_gt (hA a ha))).ne_one (Nat.dvd_one.mp hg)

/-- A positive pairwise-coprime group of denominators has a representation
by distinct prime reciprocals with the same mass only when it already is that
prime group. In particular, prime refinement cannot preserve the reciprocal
sum of any block containing a composite denominator. -/
theorem eq_of_reciprocal_sum_eq_prime_set {A B : Finset ℕ}
    (hA : ∀ a ∈ A, 1 < a)
    (hcp : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hB : ∀ b ∈ B, Nat.Prime b)
    (hs : (∑ a ∈ A, (1 : ℚ) / a) = ∑ b ∈ B, (1 : ℚ) / b) : A = B := by
  have hposA (a : ℕ) (ha : a ∈ A) : 0 < a := Nat.zero_lt_of_lt (hA a ha)
  have hposB (b : ℕ) (hb : b ∈ B) : 0 < b := (hB b hb).pos
  have hcopB : Set.Pairwise (B : Set ℕ) Nat.Coprime := by
    intro x hx y hy hne
    exact (Nat.coprime_primes (hB x hx) (hB y hy)).mpr hne
  have hDD := denom_eq_of_sum_eq hposA hposB hcp hcopB hs
  have hminp (a : ℕ) (ha : a ∈ A) : Nat.Prime a.minFac :=
    Nat.minFac_prime (Nat.ne_of_gt (hA a ha))
  have hminB (a : ℕ) (ha : a ∈ A) : a.minFac ∈ B :=
    mem_prime_group_of_dvd hB (hminp a ha) (hDD ▸ (Nat.minFac_dvd a).trans (dvd_group_product ha))
  have hbound (a : ℕ) (ha : a ∈ A) : (1 : ℚ) / a ≤ 1 / a.minFac := by
    apply one_div_le_one_div_of_le
    · exact_mod_cast (hminp a ha).pos
    · exact_mod_cast Nat.minFac_le (hposA a ha)
  have hsum_min : (∑ a ∈ A, (1 : ℚ) / a.minFac) ≤ ∑ b ∈ B, (1 : ℚ) / b := by
    have himage : (∑ p ∈ A.image Nat.minFac, (1 : ℚ) / p) =
        ∑ a ∈ A, (1 : ℚ) / a.minFac := Finset.sum_image (minFac_inj hA hcp)
    rw [← himage]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
      exact hminB a ha
    · intro p hp _
      have hpos : (0 : ℚ) < p := by exact_mod_cast (hB p hp).pos
      exact (one_div_pos.mpr hpos).le
  have hap (a : ℕ) (ha : a ∈ A) : Nat.Prime a := by
    by_contra hnp
    have hlt := (Nat.not_prime_iff_minFac_lt (hA a ha)).mp hnp
    have hqpos : (0 : ℚ) < a.minFac := by exact_mod_cast (hminp a ha).pos
    have hqlt : (a.minFac : ℚ) < a := by exact_mod_cast hlt
    have hstrict := Finset.sum_lt_sum hbound ⟨a, ha, one_div_lt_one_div_of_lt hqpos hqlt⟩
    exact (not_lt_of_ge hs.ge) (hstrict.trans_le hsum_min)
  apply Finset.Subset.antisymm
  · intro a ha
    simpa only [(hap a ha).minFac_eq] using hminB a ha
  · intro b hb
    exact mem_prime_group_of_dvd hap (hB b hb) (hDD.symm ▸ dvd_group_product hb)

#print axioms eq_of_reciprocal_sum_eq_prime_set
end Erdos307Structure
