import Erdos307CofactorSquare
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Choose.Basic

namespace Erdos307Structure

open Finset
open scoped BigOperators

private theorem jacobi_group_product_left (S : Finset ℕ) (p : ℕ) :
    jacobiSym (denom S : ℤ) p = ∏ q ∈ S, jacobiSym (q : ℤ) p := by
  induction S using Finset.induction_on with
  | empty => simp [denom, jacobiSym.one_left]
  | @insert q S hq ih =>
    rw [show denom (insert q S) = q * denom S from Finset.prod_insert hq,
      Nat.cast_mul, jacobiSym.mul_left, ih, Finset.prod_insert hq]

private theorem jacobi_group_product_right (S : Finset ℕ)
    (hS : ∀ p ∈ S, 0 < p) (t : ℤ) :
    jacobiSym t (denom S) = ∏ p ∈ S, jacobiSym t p := by
  induction S using Finset.induction_on with
  | empty => simp [denom, jacobiSym.one_right]
  | @insert p S hp ih =>
    have hp0 : p ≠ 0 := (hS p (mem_insert_self _ _)).ne'
    have hs : ∀ q ∈ S, 0 < q := fun q hq => hS q (mem_insert_of_mem hq)
    have hd : denom S ≠ 0 := (Finset.prod_pos hs).ne'
    rw [show denom (insert p S) = p * denom S from Finset.prod_insert hp,
      jacobiSym.mul_right' t hp0 hd, ih hs, Finset.prod_insert hp]

private theorem odd_prime_pair_symbol {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpo : Odd p) (hqo : Odd q) (hpq : p ≠ q) :
    jacobiSym (p : ℤ) q * jacobiSym (q : ℤ) p =
      if p % 4 = 3 ∧ q % 4 = 3 then -1 else 1 := by
  have hcop := (Nat.coprime_primes hq hp).mpr hpq.symm
  have hnonzero : (q : ℤ).gcd (p : ℤ) = 1 := by
    exact_mod_cast hcop
  have hsign := jacobiSym.eq_one_or_neg_one hnonzero
  have hrec := jacobiSym.quadratic_reciprocity_if (a := p) (b := q)
    (Nat.odd_iff.mp hpo) (Nat.odd_iff.mp hqo)
  rw [← hrec]
  by_cases h : p % 4 = 3 ∧ q % 4 = 3 <;>
    rcases hsign with he | he <;> simp [h, he]

/-- Product of the odd-support cofactor symbols, before the contribution of 2. -/
theorem odd_support_cofactor_symbol_product (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hO : ∀ p ∈ S, Odd p) :
    (∏ p ∈ S, jacobiSym (denom (S.erase p) : ℤ) p) =
      (-1 : ℤ) ^ ((S.filter fun p => p % 4 = 3).card.choose 2) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haP := hS a (mem_insert_self _ _)
    have haO := hO a (mem_insert_self _ _)
    have hp (p : ℕ) (hm : p ∈ S) := hS p (mem_insert_of_mem hm)
    have ho (p : ℕ) (hm : p ∈ S) := hO p (mem_insert_of_mem hm)
    have hterm (p : ℕ) (hm : p ∈ S) :
        jacobiSym (denom ((insert a S).erase p) : ℤ) p =
          jacobiSym (a : ℤ) p * jacobiSym (denom (S.erase p) : ℤ) p := by
      have hpne : p ≠ a := fun e => ha (e ▸ hm)
      rw [Finset.erase_insert_of_ne hpne.symm,
        show denom (insert a (S.erase p)) = a * denom (S.erase p) from
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h)),
        Nat.cast_mul, jacobiSym.mul_left]
    rw [Finset.prod_insert ha, Finset.erase_insert ha, jacobi_group_product_left _ a]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib,
      ← mul_assoc, ← Finset.prod_mul_distrib, ih hp ho]
    have hsign :
        (∏ p ∈ S, jacobiSym (p : ℤ) a * jacobiSym (a : ℤ) p) =
          (-1 : ℤ) ^ (if a % 4 = 3 then (S.filter fun p => p % 4 = 3).card else 0) := by
      calc
        _ = ∏ p ∈ S, if p % 4 = 3 ∧ a % 4 = 3 then (-1 : ℤ) else 1 := by
          apply Finset.prod_congr rfl
          intro p hm
          exact odd_prime_pair_symbol (hp p hm) haP (ho p hm) haO (fun e => ha (e ▸ hm))
        _ = _ := by
          by_cases h : a % 4 = 3
          · simp [h, ← Finset.prod_filter]
          · simp [h]
    rw [hsign, ← pow_add]
    by_cases h : a % 4 = 3
    · have hna : a ∉ S.filter (fun p => p % 4 = 3) := fun h => ha (mem_filter.mp h).1
      rw [if_pos h, Finset.filter_insert, if_pos h, Finset.card_insert_of_notMem hna]
      simp [Nat.choose_succ_succ]
    · simp [h, Finset.filter_insert]

/-- Cofactor-square signs on the even support 2·∏S imply the exact
quadratic-reciprocity sign of the odd part. -/
theorem jacobi_two_of_even_support (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (hO : ∀ p ∈ S, Odd p)
    (hcof : ∀ p ∈ S, jacobiSym ((2 : ℤ) * (denom (S.erase p) : ℤ)) p = 1) :
    jacobiSym 2 (denom S) = (-1 : ℤ) ^ ((S.filter fun p => p % 4 = 3).card.choose 2) := by
  let n := (S.filter fun p => p % 4 = 3).card.choose 2
  have hprod : jacobiSym 2 (denom S) * (-1 : ℤ) ^ n = 1 := by
    rw [jacobi_group_product_right S (fun p hp => (hS p hp).pos), show
      (-1 : ℤ) ^ n = (∏ p ∈ S, jacobiSym (denom (S.erase p) : ℤ) p) from
        (odd_support_cofactor_symbol_product S hS hO).symm,
      ← Finset.prod_mul_distrib]
    simp_rw [← jacobiSym.mul_left]
    exact (Finset.prod_congr rfl hcof).trans (Finset.prod_const_one)
  have hn : ((-1 : ℤ) ^ n) * (-1 : ℤ) ^ n = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = (jacobiSym 2 (denom S) * (-1 : ℤ) ^ n) * (-1 : ℤ) ^ n := by
      rw [mul_assoc, hn, mul_one]
    _ = _ := by rw [hprod, one_mul]

#print axioms odd_support_cofactor_symbol_product
#print axioms jacobi_two_of_even_support

end Erdos307Structure
