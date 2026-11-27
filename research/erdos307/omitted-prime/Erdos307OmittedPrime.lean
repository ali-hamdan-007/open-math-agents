import Erdos307CrossCoprime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

namespace Erdos307Structure

open Finset

/-- Homogeneous Dickson recurrence with independent sum and product variables. -/
def dicksonTrace {R : Type*} [CommRing R] (sum product : R) : ℕ → R
  | 0 => 2
  | 1 => sum
  | k + 2 => sum * dicksonTrace sum product (k + 1) -
      product * dicksonTrace sum product k

theorem dicksonTrace_add_mul {R : Type*} [CommRing R] (a b : R) (k : ℕ) :
    dicksonTrace (a+b) (a*b) k = a^k+b^k := by
  induction k using Nat.twoStepInduction with
  | zero => simp [dicksonTrace]; ring
  | one => simp [dicksonTrace]
  | more k h₀ h₁ =>
    rw [dicksonTrace, h₀, h₁]
    simp only [pow_succ]
    ring

theorem numer_union_of_disjoint {S T : Finset ℕ} (h : Disjoint S T) :
    numer (S ∪ T) = numer S * denom T + denom S * numer T := by
  have dv {U : Finset ℕ} {u : ℕ} (hu : u ∈ U) : u ∣ denom U :=
    Finset.dvd_prod_of_mem id hu
  have hp : denom (S ∪ T) = denom S * denom T := Finset.prod_union h
  simp only [numer, Finset.sum_union h, hp,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    rw [mul_comm (denom S) (denom T), Nat.mul_div_assoc _ (dv hx), mul_comm]
  · exact Finset.sum_congr rfl (fun x hx => Nat.mul_div_assoc _ (dv hx))

/-- Every omitted odd prime gives one polynomial congruence in the support
product and the sum of its cofactors, independently of its partition. -/
theorem dickson_omitted_prime {P Q : Finset ℕ} {ell : ℕ} [Fact ell.Prime]
    (hell : Odd ell)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hout : ell ∉ P ∪ Q)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    dicksonTrace (numer (P ∪ Q) : ZMod ell) ((denom (P ∪ Q) : ZMod ell)^2)
      ((ell-1)/2) = 2 := by
  have hpair {U : Finset ℕ} (hU : ∀ u ∈ U, u.Prime) :
      Set.Pairwise (U : Set ℕ) Nat.Coprime :=
    fun _ hx _ hy hxy => (Nat.coprime_primes (hU _ hx) (hU _ hy)).mpr hxy
  obtain ⟨hpq,hqp,hcross⟩ := swap_products P Q
    (fun p hp => (hP p hp).pos) (fun q hq => (hQ q hq).pos) (hpair hP) (hpair hQ) heq
  have hdis : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hc := hcross x hx x hy
    rw [Nat.Coprime, Nat.gcd_self] at hc
    exact (hP x hx).ne_one hc
  have nonzero {U : Finset ℕ} (hU : ∀ u ∈ U, u.Prime) (he : ell ∉ U) :
      (denom U : ZMod ell) ≠ 0 := by
    rw [denom, Nat.cast_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro u hu hz
    have hd := (ZMod.natCast_eq_zero_iff _ _).mp hz
    rcases (Nat.dvd_prime (hU u hu)).mp hd with h | h
    · exact (Fact.out : ell.Prime).ne_one h
    · exact he (h ▸ hu)
  have hp : (denom P : ZMod ell) ≠ 0 := nonzero hP (fun h => hout (mem_union_left _ h))
  have hq : (denom Q : ZMod ell) ≠ 0 := nonzero hQ (fun h => hout (mem_union_right _ h))
  have hN : denom (P ∪ Q) = denom Q * denom P := (Finset.prod_union hdis).trans (mul_comm _ _)
  rw [numer_union_of_disjoint hdis, hpq, hqp, hN,
    Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, mul_pow, ← pow_two, ← pow_two,
    dicksonTrace_add_mul, ← pow_mul, ← pow_mul,
    show 2 * ((ell-1)/2) = ell-1 by obtain ⟨k,hk⟩ := hell; omega,
    ZMod.pow_card_sub_one_eq_one hq, ZMod.pow_card_sub_one_eq_one hp]
  ring

/-- The complementary filter at 5 is quadratic in the two support integers. -/
theorem omitted_five {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hout : 5 ∉ P ∪ Q)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    (numer (P ∪ Q) : ZMod 5)^2 - 2*(denom (P ∪ Q) : ZMod 5)^2 = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := dickson_omitted_prime (by decide : Odd (5 : ℕ)) hP hQ hout heq
  change dicksonTrace (numer (P ∪ Q) : ZMod 5) ((denom (P ∪ Q) : ZMod 5)^2) 2 = 2 at h
  simpa [dicksonTrace, pow_two, mul_comm] using h

/-- The complementary filter at 7 is cubic in the two support integers. -/
theorem omitted_seven {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hout : 7 ∉ P ∪ Q)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    (numer (P ∪ Q) : ZMod 7)^3 -
      3*(denom (P ∪ Q) : ZMod 7)^2*(numer (P ∪ Q) : ZMod 7) = 2 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h := dickson_omitted_prime (by decide : Odd (7 : ℕ)) hP hQ hout heq
  change dicksonTrace (numer (P ∪ Q) : ZMod 7) ((denom (P ∪ Q) : ZMod 7)^2) 3 = 2 at h
  rw [← h]
  simp only [dicksonTrace]
  ring

#print axioms dickson_omitted_prime
#print axioms omitted_five
#print axioms omitted_seven

end Erdos307Structure
