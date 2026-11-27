import A056777Parity
import Mathlib.Data.Nat.Totient

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenRepeatedFour

private theorem prime_of_length_one {n : ℕ} (hn : n ≠ 0)
    (h : n.primeFactorsList.length = 1) : n.Prime := by
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp h
  have hprod := Nat.prod_primeFactorsList hn
  rw [hp, List.prod_singleton] at hprod
  have hmem : p ∈ n.primeFactorsList := by simp [hp]
  exact hprod ▸ Nat.prime_of_mem_primeFactorsList hmem

private theorem no_square_endpoints {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (hgap : n + 12 = m ∨ m + 12 = n) (hσ : σ 1 n + m = σ 1 m + n) :
    (¬ ((∃ k : ℕ, n = k ^ 2) ∨ ∃ k : ℕ, n = 2 * k ^ 2)) ∧
    (¬ ((∃ k : ℕ, m = k ^ 2) ∨ ∃ k : ℕ, m = 2 * k ^ 2)) := by
  rcases hgap with he | he
  · subst m
    exact A056777Parity.no_square_shapes_of_sigma_step hn (by omega)
  · subst n
    exact (A056777Parity.no_square_shapes_of_sigma_step hm (by omega)).symm

private theorem no_four_times_prime_pair {q m : ℕ} (hq : q.Prime) (hq₂ : q ≠ 2)
    (hml : m.primeFactorsList.length = 4) (hgap : 4 * q + 12 = m ∨ m + 12 = 4 * q)
    (hφ : (4 * q).totient + m = m.totient + 4 * q)
    (hmns : ¬ ∃ k : ℕ, m = k ^ 2) : False := by
  have hqo := hq.odd_of_ne_two hq₂
  have hqmod := Nat.odd_iff.mp hqo
  have hm₈ : 8 ∣ m := by omega
  obtain ⟨t, rfl⟩ := hm₈
  have ht₀ : t ≠ 0 := by rintro rfl; simp at hml
  have hlen := (Nat.perm_primeFactorsList_mul (by decide : (8 : ℕ) ≠ 0) ht₀).length_eq
  rw [List.length_append, hml,
    show (8 : ℕ).primeFactorsList.length = 3 by
      rw [show (8 : ℕ) = 2 ^ 3 by decide, Nat.prime_two.primeFactorsList_pow,
        List.length_replicate]] at hlen
  have ht := prime_of_length_one ht₀ (by omega : t.primeFactorsList.length = 1)
  have ht₂ : t ≠ 2 := by
    rintro rfl
    exact hmns ⟨4, by decide⟩
  have hqcop : (4 : ℕ).Coprime q := by
    simpa using hqo.coprime_two_left.pow_left 2
  have htcop : (8 : ℕ).Coprime t := by
    simpa using (ht.odd_of_ne_two ht₂).coprime_two_left.pow_left 3
  rw [Nat.totient_mul hqcop, Nat.totient_mul htcop, Nat.totient_prime hq,
    Nat.totient_prime ht, show (4 : ℕ).totient = 2 by decide,
    show (8 : ℕ).totient = 4 by decide] at hφ
  have := hq.pos
  have := ht.pos
  omega

/-- An even length-three endpoint of the form `p²q` cannot have a length-four partner
at distance twelve with the same totient deficit and divisor surplus. -/
theorem no_even_repeated_three_four_pair {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : Even (p ^ 2 * q)) (hm : m.primeFactorsList.length = 4)
    (hgap : p ^ 2 * q + 12 = m ∨ m + 12 = p ^ 2 * q)
    (hφ : (p ^ 2 * q).totient + m = m.totient + p ^ 2 * q)
    (hσ : σ 1 (p ^ 2 * q) + m = σ 1 m + p ^ 2 * q) : False := by
  have hn₀ : p ^ 2 * q ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero
  have hm₀ : m ≠ 0 := by rintro rfl; simp at hm
  have hshapes := no_square_endpoints hn₀ hm₀ hgap hσ
  rcases hp.eq_two_or_odd' with rfl | hpo
  · exact no_four_times_prime_pair hq hpq.symm hm hgap hφ (fun hs => hshapes.2 (Or.inl hs))
  rcases hq.eq_two_or_odd' with rfl | hqo
  · exact hshapes.1 (Or.inr ⟨p, by rw [Nat.mul_comm]⟩)
  exact (Nat.not_even_iff_odd.mpr ((hpo.pow).mul hqo)) he

end A056777EvenRepeatedFour

#print axioms A056777EvenRepeatedFour.no_even_repeated_three_four_pair
