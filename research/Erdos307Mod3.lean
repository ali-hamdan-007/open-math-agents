import Erdos307CrossCoprime
import Mathlib.Algebra.Field.ZMod

open Finset
open scoped BigOperators

namespace Erdos307Structure

private lemma zmod_three_inv_self (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  fin_cases x <;> first | exact (hx rfl).elim | decide

theorem numer_mod_three {A : Finset ℕ}
    (hA : ∀ a ∈ A, (a : ZMod 3) ≠ 0) :
    (numer A : ZMod 3) = (denom A : ZMod 3) * ∑ a ∈ A, (a : ZMod 3) := by
  rw [numer, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hdiv : a ∣ denom A :=
    ⟨denom (A.erase a), by simpa [denom, mul_comm] using (Finset.prod_erase_mul A id ha).symm⟩
  have hmul : (denom A / a : ℕ) * a = denom A := Nat.div_mul_cancel hdiv
  have hcast : ((denom A / a : ℕ) : ZMod 3) * (a : ZMod 3) = (denom A : ZMod 3) := by
    exact (Nat.cast_mul _ _).symm.trans (congrArg (fun t : ℕ => (t : ZMod 3)) hmul)
  calc
    _ = ((denom A / a : ℕ) : ZMod 3) * ((a : ZMod 3) * (a : ZMod 3)) := by
      rw [zmod_three_inv_self _ (hA a ha), mul_one]
    _ = _ := by rw [← mul_assoc, hcast]

private lemma denom_cast_ne_zero_mod_three {A : Finset ℕ}
    (hA : ∀ a ∈ A, (a : ZMod 3) ≠ 0) : (denom A : ZMod 3) ≠ 0 := by
  rw [denom, Nat.cast_prod]
  exact Finset.prod_ne_zero_iff.mpr hA

/-- When both sides avoid multiples of three, each side's signed residue sum equals
the product of all its denominators and the other side's denominators modulo three. -/
theorem swap_mod_three_of_units {P Q : Finset ℕ}
    (hp : ∀ p ∈ P, (p : ZMod 3) ≠ 0) (hq : ∀ q ∈ Q, (q : ZMod 3) ≠ 0)
    (hPQ : numer P = denom Q) (hQP : numer Q = denom P) :
    (∑ p ∈ P, (p : ZMod 3)) = (denom P : ZMod 3) * (denom Q : ZMod 3) ∧
    (∑ q ∈ Q, (q : ZMod 3)) = (denom P : ZMod 3) * (denom Q : ZMod 3) := by
  have h1 := numer_mod_three hp
  have h2 := numer_mod_three hq
  rw [hPQ] at h1
  rw [hQP] at h2
  constructor
  · calc
      _ = (denom P : ZMod 3) * ((denom P : ZMod 3) * ∑ p ∈ P, (p : ZMod 3)) := by
        rw [← mul_assoc, zmod_three_inv_self _ (denom_cast_ne_zero_mod_three hp), one_mul]
      _ = _ := by rw [← h1]
  · calc
      _ = (denom Q : ZMod 3) * ((denom Q : ZMod 3) * ∑ q ∈ Q, (q : ZMod 3)) := by
        rw [← mul_assoc, zmod_three_inv_self _ (denom_cast_ne_zero_mod_three hq), one_mul]
      _ = _ := by rw [← h2, mul_comm]

/-- If one side has a multiple of three, the other side's signed residue sum is zero. -/
theorem swap_mod_three_of_dvd {P Q : Finset ℕ}
    (hp : (denom P : ZMod 3) = 0) (hq : ∀ q ∈ Q, (q : ZMod 3) ≠ 0)
    (hQP : numer Q = denom P) :
    (∑ q ∈ Q, (q : ZMod 3)) = 0 := by
  have h := numer_mod_three hq
  rw [hQP, hp] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (denom_cast_ne_zero_mod_three hq)


/-- If a member of one side is divisible by three, the product of all other
denominators is one modulo three. -/
theorem swap_mod_three_product_of_mem_zero {P Q : Finset ℕ} {p : ℕ}
    (hp : p ∈ P) (hp0 : (p : ZMod 3) = 0)
    (hP : ∀ a ∈ P, 0 < a) (hQ : ∀ q ∈ Q, (q : ZMod 3) ≠ 0)
    (hPQ : numer P = denom Q) :
    (denom (P.erase p) : ZMod 3) * (denom Q : ZMod 3) = 1 := by
  have hcofactor {a : ℕ} (ha : a ∈ P) :
      denom P / a = denom (P.erase a) := by
    have hmul : denom (P.erase a) * a = denom P := Finset.prod_erase_mul P id ha
    rw [← hmul, Nat.mul_div_cancel _ (hP a ha)]
  have hsum : (∑ a ∈ P.erase p, ((denom P / a : ℕ) : ZMod 3)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hcofactor (Finset.mem_of_mem_erase ha), denom, Nat.cast_prod]
    have hpa : p ∈ P.erase a :=
      Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase ha).symm, hp⟩
    rw [← Finset.prod_erase_mul _ _ hpa, hp0, mul_zero]
  have heq : (numer P : ZMod 3) = (denom (P.erase p) : ZMod 3) := by
    rw [numer, Nat.cast_sum, ← Finset.sum_erase_add _ _ hp, hsum, zero_add, hcofactor hp]
  rw [hPQ] at heq
  rw [← heq, zmod_three_inv_self _ (denom_cast_ne_zero_mod_three hQ)]

end Erdos307Structure
