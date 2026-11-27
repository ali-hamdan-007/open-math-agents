import Erdos307FrameOneTest
import PrimeBudget
import Mathlib.Tactic.Linarith

open Finset
open scoped BigOperators

namespace Erdos307Structure

/-- For fixed base products M,N and left cofactor sum U, the viable right
cofactor values are obtained by dividing the differences from divisors of U*N+M². -/
theorem frame_right_cofactor_values {M U N : ℕ} (hU : 0 < U) :
    {V : ℕ | U * V < M * N ∧ (M * N - U * V) ∣ U * N + M ^ 2} =
      (fun d : ℕ => (M * N - d) / U) ''
        {d : ℕ | 0 < d ∧ d ≤ M * N ∧ d ∣ U * N + M ^ 2 ∧ U ∣ M * N - d} := by
  ext V
  constructor
  · rintro ⟨hlt, hdvd⟩
    let d := M * N - U * V
    have heq : M * N - d = U * V := by dsimp [d]; omega
    refine ⟨d, ⟨Nat.sub_pos_of_lt hlt, Nat.sub_le _ _, hdvd, ?_⟩, ?_⟩
    · rw [heq]
      exact dvd_mul_right U V
    · change (M * N - d) / U = V
      rw [heq, Nat.mul_div_cancel_left _ hU]
  · rintro ⟨d, ⟨hd0, hdN, hdvd, hdiv⟩, rfl⟩
    have heq : U * ((M * N - d) / U) = M * N - d :=
      by rw [mul_comm, Nat.div_mul_cancel hdiv]
    exact ⟨by rw [heq]; omega, by rw [heq, show M * N - (M * N - d) = d by omega]; exact hdvd⟩

/-- A prime right completion numerator forces determinant one if the new right
denominator is at least two. -/
theorem frame_det_eq_one_of_prime {M U N V : ℕ}
    (hprime : Nat.Prime (U * N + M ^ 2))
    (hdiv : (M * N - U * V) ∣ U * N + M ^ 2)
    (hquot : 2 ≤ (U * N + M ^ 2) / (M * N - U * V)) :
    M * N - U * V = 1 := by
  obtain h | h := (Nat.dvd_prime hprime).mp hdiv
  · exact h
  · rw [h, Nat.div_self hprime.pos] at hquot
    omega

private theorem reciprocal_clearing (Q : Finset ℕ) (hQ : ∀ q ∈ Q, 1 < q) :
    (denom Q : ℚ) * (∑ q ∈ Q, (1 : ℚ) / q) = numer Q := by
  rw [numer, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hq0 : q ≠ 0 := by have := hQ q hq; omega
  have hq0' : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hdiv : q ∣ denom Q :=
    ⟨denom (Q.erase q), by simpa [denom, mul_comm] using (Finset.prod_erase_mul Q id hq).symm⟩
  rw [mul_one_div]
  apply (div_eq_iff hq0').mpr
  exact_mod_cast (Nat.div_mul_cancel hdiv).symm

/-- When the left base is one denominator M, its cofactor is 1. With a prime
right completion numerator, the opposite base needs at least 59 members once
its product reaches 1000. -/
theorem frame_card_ge_59_of_singleton_base_prime_completion {M : ℕ} {Q : Finset ℕ}
    (hM : 2 ≤ M) (hQ : ∀ q ∈ Q, 1 < q)
    (hcop : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (hN : 1000 ≤ denom Q) (hlt : numer Q < M * denom Q)
    (hprime : Nat.Prime (denom Q + M ^ 2))
    (hdiv : (M * denom Q - numer Q) ∣ denom Q + M ^ 2)
    (hquot : 2 ≤ (denom Q + M ^ 2) / (M * denom Q - numer Q)) :
    59 ≤ Q.card := by
  have hdet : M * denom Q - numer Q = 1 := by
    simpa using frame_det_eq_one_of_prime (M := M) (U := 1) (N := denom Q)
      (V := numer Q) (by simpa using hprime) (by simpa using hdiv) (by simpa using hquot)
  have hvalue : numer Q + 1 = M * denom Q := by omega
  have hclear := reciprocal_clearing Q hQ
  have hNq : (1000 : ℚ) ≤ denom Q := by exact_mod_cast hN
  have hMq : (2 : ℚ) ≤ M := by exact_mod_cast hM
  have hvalueq : (numer Q : ℚ) + 1 = M * (denom Q : ℚ) := by exact_mod_cast hvalue
  by_contra hn
  have hs := pairwise_coprime_reciprocal_margin_of_card_le_58 hQ hcop (by omega)
  have hmul := mul_lt_mul_of_pos_left hs (show (0 : ℚ) < denom Q by linarith)
  rw [hclear] at hmul
  have hlower := mul_le_mul_of_nonneg_right hMq (show (0 : ℚ) ≤ denom Q by linarith)
  linarith

end Erdos307Structure
