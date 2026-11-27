import A056777Closure
import A056777Parity
import Mathlib.Data.Nat.Squarefree

/-!
# Odd squarefree pairs in the A056777 conjecture

The A056777 converse, also formulated as Choudhury–Wei Conjecture 1.1, holds when
both arguments are odd and squarefree. Previous A056777 work in Kuberwastaken/c5-k4
formalizes the small-excess classification used in the one-sided semiprime step.
Here the divisor-sum shift by 12 forces one of the arguments to be semiprime.
-/

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Squarefree

private theorem geom_odd_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp]
    simp [Nat.add_mod]

/-- Each odd prime with odd exponent contributes at least one factor of two
to the divisor sum. -/
theorem two_pow_card_odd_exponents_dvd_sigma {n : ℕ} (hn : n ≠ 0) :
    2 ^ (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ∣ σ 1 n := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  let s := n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)
  let f (p : ℕ) := ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i
  change 2 ^ s.card ∣ ∏ p ∈ n.primeFactors, f p
  have hsub : s ⊆ n.primeFactors := Finset.filter_subset _ _
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset s n.primeFactors f hsub)
  rw [← Finset.prod_const]
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have ⟨hmem, hp2, hexp⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primeFactors hmem
  have hodd := hprime.eq_two_or_odd.resolve_left hp2
  apply Nat.dvd_of_mod_eq_zero
  dsimp [f]
  rw [geom_odd_mod_two hodd]
  have := Nat.odd_iff.mp hexp
  omega

/-- The divisor-sum step by twelve forces at least one endpoint to have
at most two odd primes occurring to odd exponents. -/
theorem at_most_two_odd_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)).card ≤ 2 ∨
    ((n + 12).primeFactors.filter fun p => p ≠ 2 ∧ Odd ((n + 12).factorization p)).card ≤ 2 := by
  by_contra! h
  have h₁ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.1))
    (two_pow_card_odd_exponents_dvd_sigma hn)
  have h₂ := dvd_trans (pow_dvd_pow 2 (show 3 ≤ _ from h.2))
    (two_pow_card_odd_exponents_dvd_sigma (show n + 12 ≠ 0 by omega))
  change 8 ∣ σ 1 n at h₁
  change 8 ∣ σ 1 (n + 12) at h₂
  omega

private theorem filter_eq_primeFactors {n : ℕ} (hs : Squarefree n) (ho : Odd n) :
    (n.primeFactors.filter fun p => p ≠ 2 ∧ Odd (n.factorization p)) = n.primeFactors := by
  apply Finset.filter_eq_self.mpr
  intro p hp
  have ⟨hprime, hdiv, hn⟩ := Nat.mem_primeFactors.mp hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Nat.odd_iff.mp ho
    omega
  have hpos := hprime.factorization_pos_of_dvd hn hdiv
  have hle := hs.natFactorization_le_one p
  have he : n.factorization p = 1 := by omega
  exact ⟨hp2, he ▸ (by decide : Odd 1)⟩

private theorem factor_count_eq_of_squarefree {n : ℕ} (hs : Squarefree n) :
    n.primeFactors.card = n.primeFactorsList.length := by
  rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hs.nodup_primeFactorsList]

/-- The A056777 pair comes from a prime quadruple if both endpoints are odd and squarefree. -/
theorem prime_quadruple_of_odd_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (ho : Odd n)
    (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_contra h
  obtain ⟨hc₁, hc₂⟩ := A056777Closure.factor_count_of_counterexample hn hnp ht hs h
  have ho' : Odd (n + 12) := by
    rw [Nat.odd_iff]
    have := Nat.odd_iff.mp ho
    omega
  have hcount := at_most_two_odd_exponents_of_sigma_step (show n ≠ 0 by omega) hs
  rw [filter_eq_primeFactors h₁ ho, filter_eq_primeFactors h₂ ho',
    factor_count_eq_of_squarefree h₁, factor_count_eq_of_squarefree h₂] at hcount
  omega

end A056777Squarefree

#print axioms A056777Squarefree.at_most_two_odd_exponents_of_sigma_step
#print axioms A056777Squarefree.prime_quadruple_of_odd_squarefree_pair
