import A056777Closure
import A056777Parity
import Mathlib.Data.Nat.Squarefree

/-!
# Odd squarefree pairs in the A056777 conjecture

The converse in [OEIS A056777](https://oeis.org/A056777) is Conjecture 1.1 of
[Choudhury and Wei](https://arxiv.org/abs/2606.10331). Their Theorem 2.2 covers
pairs of squarefree semiprimes. [Previous formal work](https://github.com/Kuberwastaken/c5-k4)
also covers the small-excess classification used in the one-sided semiprime step.
The divisor-sum shift by twelve forces one of the arguments to be semiprime
when both arguments are odd and squarefree.
-/

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Squarefree

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
  rw [A056777Parity.geom_odd_mod_two hodd]
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

private theorem dvd_eight_sigma_of_card_ge_three {n : ℕ} (hn : Squarefree n) (ho : Odd n)
    (hc : 3 ≤ n.primeFactors.card) : 8 ∣ σ 1 n := by
  have h := two_pow_card_odd_exponents_dvd_sigma (n := n) hn.ne_zero
  rw [filter_eq_primeFactors hn ho] at h
  exact (pow_dvd_pow 2 hc).trans h

private theorem low_excess_of_card_le_two {n : ℕ} (hn : Squarefree n)
    (hc : n.primeFactors.card ≤ 2) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 := by
  by_cases hn1 : n = 1
  · subst n
    simp
  by_cases hp : n.Prime
  · left
    have hσ : σ 1 n = n + 1 := by simpa using sigma_one_apply_prime_pow (i := 1) hp
    rw [hσ, Nat.totient_prime hp]
    have := hp.one_lt
    omega
  · right
    have hnn : 1 < n := by have := hn.ne_zero; omega
    have hh (h : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) : False := by
      have hlen := A056777Closure.factor_count_of_nonsemiprime hnn hp h
      rw [← factor_count_eq_of_squarefree hn] at hlen
      omega
    obtain ⟨p, q, hpp, hq, rfl⟩ := not_not.mp (fun h => hh h)
    have hne : p ≠ q := by
      rintro rfl
      exact (Nat.squarefree_iff_prime_squarefree.mp hn p hpp) (dvd_refl _)
    exact (A056777Closure.excess_two_iff _).mpr ⟨p, q, hpp, hq, hne, rfl⟩

/-- The A056777 conditions are incompatible with both endpoints being even and squarefree. -/
theorem no_even_squarefree_pair {n : ℕ}
    (he : Even n) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  obtain ⟨m, hm⟩ := he
  have hn : n = 2 * m := by omega
  have hn' : n + 12 = 2 * (m + 6) := by omega
  rw [hn] at h₁
  rw [hn'] at h₂
  have hcop₁ := Nat.coprime_of_squarefree_mul h₁
  have hcop₂ := Nat.coprime_of_squarefree_mul h₂
  have ho₁ := hcop₁.odd_of_left
  have ho₂ := hcop₂.odd_of_left
  have hsq₁ := h₁.squarefree_of_dvd (dvd_mul_left m 2)
  have hsq₂ := h₂.squarefree_of_dvd (dvd_mul_left (m + 6) 2)
  rw [hn', hn, Nat.totient_mul hcop₁, Nat.totient_mul hcop₂] at ht
  norm_num at ht
  rw [hn', hn, isMultiplicative_sigma.map_mul_of_coprime hcop₁,
    isMultiplicative_sigma.map_mul_of_coprime hcop₂, show σ 1 2 = 3 by decide] at hs
  have hadd : σ 1 (m + 6) = σ 1 m + 4 := by omega
  have hsmall : m.primeFactors.card ≤ 2 ∨ (m + 6).primeFactors.card ≤ 2 := by
    by_contra! h
    have hd₁ := dvd_eight_sigma_of_card_ge_three hsq₁ ho₁ (by omega)
    have hd₂ := dvd_eight_sigma_of_card_ge_three hsq₂ ho₂ (by omega)
    omega
  rcases hsmall with hc | hc
  · rcases low_excess_of_card_le_two hsq₁ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree (m + 6) ho₂ hsq₂ with h' | h' | h' <;>
      omega
  · rcases low_excess_of_card_le_two hsq₂ hc with h | h <;>
      rcases A056777Closure.low_excess_of_odd_squarefree m ho₁ hsq₁ with h' | h' | h' <;>
      omega

/-- The A056777 converse holds whenever both endpoints are squarefree. -/
theorem prime_quadruple_of_squarefree_pair {n : ℕ}
    (hn : 1 < n) (hnp : ¬n.Prime) (h₁ : Squarefree n) (h₂ : Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_cases he : Even n
  · exact (no_even_squarefree_pair he h₁ h₂ ht hs).elim
  · exact prime_quadruple_of_odd_squarefree_pair hn hnp
      (Nat.not_even_iff_odd.mp he) h₁ h₂ ht hs

/-- The remaining cases of the A056777 converse have a repeated prime factor
in at least one endpoint. -/
theorem reduction_to_nonsquarefree_endpoint
    (hremaining : ∀ n : ℕ, 1 < n → ¬n.Prime →
      (n + 12).totient = n.totient + 12 → σ 1 (n + 12) = σ 1 n + 12 →
      (¬Squarefree n ∨ ¬Squarefree (n + 12)) →
      ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
        (p + 8).Prime ∧ n = p * (p + 8))
    {n : ℕ} (hn : 1 < n) (hnp : ¬n.Prime)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  by_cases h₁ : Squarefree n
  · by_cases h₂ : Squarefree (n + 12)
    · exact prime_quadruple_of_squarefree_pair hn hnp h₁ h₂ ht hs
    · exact hremaining n hn hnp ht hs (Or.inr h₂)
  · exact hremaining n hn hnp ht hs (Or.inl h₁)

end A056777Squarefree

#print axioms A056777Squarefree.at_most_two_odd_exponents_of_sigma_step
#print axioms A056777Squarefree.prime_quadruple_of_odd_squarefree_pair
#print axioms A056777Squarefree.prime_quadruple_of_squarefree_pair
#print axioms A056777Squarefree.reduction_to_nonsquarefree_endpoint
