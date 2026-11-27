import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Field.Basic

open Finset
open scoped BigOperators

namespace Erdos307Structure

private def smallPrimes : Finset ℕ := (Finset.range 271).filter Nat.Prime

private def primeWeight (p : ℕ) : ℚ := max (1 / (p : ℚ) - 1 / 271) 0

private theorem primeWeight_small {p : ℕ} (hp : p.Prime) (hlt : p < 271) :
    primeWeight p = 1 / (p : ℚ) - 1 / 271 := by
  have hpos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hle : (p : ℚ) ≤ 271 := by exact_mod_cast hlt.le
  exact max_eq_left (sub_nonneg.mpr (one_div_le_one_div_of_le hpos hle))

private theorem primeWeight_large {p : ℕ} (hle : 271 ≤ p) : primeWeight p = 0 := by
  have hcast : (271 : ℚ) ≤ p := by exact_mod_cast hle
  exact max_eq_right (sub_nonpos.mpr (one_div_le_one_div_of_le (by norm_num) hcast))

theorem prime_budget_sum {S : Finset ℕ} (hp : ∀ p ∈ S, Nat.Prime p) :
    (∑ p ∈ S, max ((1 : ℚ) / p - 1 / 271) 0) ≤
      ∑ p ∈ (Finset.range 271).filter Nat.Prime, ((1 : ℚ) / p - 1 / 271) := by
  change (∑ p ∈ S, primeWeight p) ≤ ∑ p ∈ smallPrimes, _
  have hs : S.filter (· < 271) ⊆ smallPrimes := by
    intro p h
    obtain ⟨hm, hlt⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hp p hm⟩
  calc
    (∑ p ∈ S, primeWeight p) = ∑ p ∈ S.filter (· < 271), primeWeight p := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hm hn
      exact primeWeight_large (Nat.le_of_not_gt (fun hlt => hn (Finset.mem_filter.mpr ⟨hm, hlt⟩)))
    _ ≤ ∑ p ∈ smallPrimes, primeWeight p :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => le_max_right _ _)
    _ = ∑ p ∈ smallPrimes, ((1 : ℚ) / p - 1 / 271) := by
      apply Finset.sum_congr rfl
      intro p hm
      obtain ⟨hr, hprime⟩ := Finset.mem_filter.mp hm
      exact primeWeight_small hprime (Finset.mem_range.mp hr)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem prime_budget_numeric :
    (∑ p ∈ (Finset.range 271).filter Nat.Prime, ((1 : ℚ) / p - 1 / 271)) + 58 / 271 <
      1999 / 1000 := by
  decide +kernel

theorem prime_budget_margin {S : Finset ℕ} (hp : ∀ p ∈ S, Nat.Prime p) :
    (∑ p ∈ S, max ((1 : ℚ) / p - 1 / 271) 0) + 58 / 271 < 1999 / 1000 :=
  lt_of_le_of_lt (add_le_add_left (prime_budget_sum hp) _) prime_budget_numeric

theorem prime_budget {S : Finset ℕ} (hp : ∀ p ∈ S, Nat.Prime p) :
    (∑ p ∈ S, max ((1 : ℚ) / p - 1 / 271) 0) + 58 / 271 < 2 :=
  lt_trans (prime_budget_margin hp) (by norm_num)


private theorem minFac_injOn {A : Finset ℕ} (hA : ∀ a ∈ A, 1 < a)
    (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    Set.InjOn Nat.minFac (A : Set ℕ) := by
  intro a ha b hb he
  by_contra hn
  have hg := Nat.dvd_gcd (Nat.minFac_dvd a) (he ▸ Nat.minFac_dvd b)
  rw [hcop ha hb hn] at hg
  exact (Nat.minFac_prime (Nat.ne_of_gt (hA a ha))).ne_one (Nat.dvd_one.mp hg)

private theorem minFac_weight_bound {a : ℕ} (ha : 1 < a) :
    (1 : ℚ) / a ≤ 1 / 271 + primeWeight a.minFac := by
  have hmin : (0 : ℚ) < a.minFac := by
    exact_mod_cast (Nat.minFac_prime (Nat.ne_of_gt ha)).pos
  have hle : (a.minFac : ℚ) ≤ a := by exact_mod_cast Nat.minFac_le (by omega : 0 < a)
  have hr := one_div_le_one_div_of_le hmin hle
  have hw : (1 : ℚ) / a.minFac - 1 / 271 ≤ primeWeight a.minFac := le_max_left _ _
  linarith

private theorem minFac_budget_bound {A : Finset ℕ} (hA : ∀ a ∈ A, 1 < a)
    (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    (∑ a ∈ A, primeWeight a.minFac) + 58 / 271 < 1999 / 1000 := by
  rw [← Finset.sum_image (minFac_injOn hA hcop)]
  exact prime_budget_margin (fun p hp => by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.minFac_prime (Nat.ne_of_gt (hA a ha)))

theorem pairwise_coprime_reciprocal_margin_of_card_le_58 {A : Finset ℕ}
    (hA : ∀ a ∈ A, 1 < a) (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hcard : A.card ≤ 58) :
    (∑ a ∈ A, (1 : ℚ) / a) < 1999 / 1000 := by
  have hr := Finset.sum_le_sum (fun a ha => minFac_weight_bound (hA a ha))
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hr
  have hc : (A.card : ℚ) ≤ 58 := by exact_mod_cast hcard
  have hw := minFac_budget_bound hA hcop
  linarith

theorem pairwise_coprime_reciprocal_lt_two_of_card_le_59_of_composite {A : Finset ℕ}
    (hA : ∀ a ∈ A, 1 < a) (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hcard : A.card ≤ 59) {a : ℕ} (ha : a ∈ A) (hcomp : ¬ a.Prime) :
    (∑ b ∈ A, (1 : ℚ) / b) < 2 := by
  have ha0 : 0 < a := by have := hA a ha; omega
  have hpsq := Nat.minFac_sq_le_self ha0 hcomp
  by_cases hp : 32 ≤ a.minFac
  · have h1024 : 1024 ≤ a := calc
      1024 = 32 ^ 2 := by norm_num
      _ ≤ a.minFac ^ 2 := Nat.pow_le_pow_left hp 2
      _ ≤ a := hpsq
    have hcast : (1024 : ℚ) ≤ a := by exact_mod_cast h1024
    have hsmall := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 1024) hcast
    have hrest := pairwise_coprime_reciprocal_margin_of_card_le_58
      (A := A.erase a) (fun b hb => hA b (Finset.mem_of_mem_erase hb))
      (fun _ hb _ hc hne => hcop (Finset.mem_of_mem_erase hb) (Finset.mem_of_mem_erase hc) hne)
      (by rw [Finset.card_erase_of_mem ha]; omega)
    rw [← Finset.sum_erase_add _ _ ha]
    linarith
  · have hp2 : 2 ≤ a.minFac := (Nat.minFac_prime (Nat.ne_of_gt (hA a ha))).two_le
    have htwo : 2 * a.minFac ≤ a :=
      (Nat.mul_le_mul_right _ hp2).trans (by simpa [pow_two] using hpsq)
    have hcast : (2 : ℚ) * a.minFac ≤ a := by exact_mod_cast htwo
    have hpos : (0 : ℚ) < a.minFac := by exact_mod_cast (by omega : 0 < a.minFac)
    have hr := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 * a.minFac) hcast
    have h32 : (a.minFac : ℚ) ≤ 32 := by exact_mod_cast (by omega : a.minFac ≤ 32)
    have hi := one_div_le_one_div_of_le hpos h32
    have he : (1 : ℚ) / (2 * a.minFac) = (1 / (a.minFac : ℚ)) / 2 := by
      rw [div_div, mul_comm]
    rw [he] at hr
    have hw : (1 : ℚ) / a.minFac - 1 / 271 ≤ primeWeight a.minFac := le_max_left _ _
    have hsave : (1 : ℚ) / a ≤ 1 / 271 + primeWeight a.minFac - 1 / 64 := by linarith
    have hrest : (∑ b ∈ A.erase a, (1 : ℚ) / b) ≤
        ∑ b ∈ A.erase a, (1 / 271 + primeWeight b.minFac) :=
      Finset.sum_le_sum (fun b hb => minFac_weight_bound (hA b (Finset.mem_of_mem_erase hb)))
    have hsum := Finset.sum_erase_add A (fun b => 1 / 271 + primeWeight b.minFac) ha
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum hrest
    rw [← Finset.sum_erase_add _ _ ha]
    have hc : (A.card : ℚ) ≤ 59 := by exact_mod_cast hcard
    have hbudget := minFac_budget_bound hA hcop
    linarith


theorem card_ge_59_of_pairwise_coprime_reciprocal_sum_ge_two {A : Finset ℕ}
    (hA : ∀ a ∈ A, 1 < a) (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hsum : (2 : ℚ) ≤ ∑ a ∈ A, (1 : ℚ) / a) : 59 ≤ A.card := by
  by_contra hcard
  have hsmall := pairwise_coprime_reciprocal_margin_of_card_le_58 hA hcop (by omega)
  linarith

theorem prime_of_pairwise_coprime_reciprocal_sum_ge_two_of_card_le_59 {A : Finset ℕ}
    (hA : ∀ a ∈ A, 1 < a) (hcop : Set.Pairwise (A : Set ℕ) Nat.Coprime)
    (hsum : (2 : ℚ) ≤ ∑ a ∈ A, (1 : ℚ) / a) (hcard : A.card ≤ 59) :
    ∀ a ∈ A, a.Prime := by
  intro a ha
  by_contra hn
  exact (not_lt_of_ge hsum)
    (pairwise_coprime_reciprocal_lt_two_of_card_le_59_of_composite hA hcop hcard ha hn)

end Erdos307Structure
