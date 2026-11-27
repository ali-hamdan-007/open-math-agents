import Mathlib.Data.Nat.Totient

namespace A056777
open Finset Nat

/-- Every distinct odd prime factor contributes at least one factor of two
to the totient. A factor 2^a contributes a further a-1 factors of two. -/
theorem two_power_budget_dvd_totient (n : ℕ) (hn : n ≠ 0) :
    2 ^ ((n.primeFactors.erase 2).card + (n.factorization 2 - 1)) ∣ n.totient := by
  let f (p : ℕ) := p ^ (n.factorization p - 1) * (p - 1)
  have oddpart : 2 ^ (n.primeFactors.erase 2).card ∣ ∏ p ∈ n.primeFactors.erase 2, f p := by
    rw [← Finset.prod_const]
    apply Finset.prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨hne,hm⟩ := mem_erase.mp hp
    have hop := (prime_of_mem_primeFactors hm).odd_of_ne_two hne
    have hp1 := (prime_of_mem_primeFactors hm).two_le
    apply dvd_mul_of_dvd_right
    have := Nat.odd_iff.mp hop
    omega
  rw [Nat.totient_eq_prod_factorization hn,Finsupp.prod,Nat.support_factorization,pow_add]
  change _ ∣ ∏ p ∈ n.primeFactors, f p
  by_cases h : 2 ∈ n.primeFactors
  · rw [← Finset.prod_erase_mul _ f h]
    apply Nat.mul_dvd_mul oddpart
    simp [f]
  · have hzero : n.factorization 2 = 0 := by
      by_contra hne
      exact h (Nat.mem_primeFactors.mpr ⟨Nat.prime_two,Nat.dvd_of_factorization_pos
        hne,hn⟩)
    simpa [hzero,Finset.erase_eq_of_notMem h] using oddpart

/-- For endpoints separated by twelve with equal totient defects, at least one
has at most two distinct odd primes after accounting for the power of two. -/
theorem at_most_two_totient_contributions {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (gap : n+12=m ∨ m+12=n) (balance : n.totient+m = m.totient+n) :
    (n.primeFactors.erase 2).card + (n.factorization 2 - 1) ≤ 2 ∨
    (m.primeFactors.erase 2).card + (m.factorization 2 - 1) ≤ 2 := by
  by_contra! h
  have eight (x : ℕ) (hx : x ≠ 0)
      (hb : 2 < (x.primeFactors.erase 2).card + (x.factorization 2 - 1)) :
      8 ∣ x.totient :=
    (pow_dvd_pow 2 (show 3 ≤ _ from hb)).trans (two_power_budget_dvd_totient x hx)
  obtain ⟨u,hu⟩ := eight n hn h.1
  obtain ⟨v,hv⟩ := eight m hm h.2
  rcases gap with hg | hg <;> omega

#print axioms at_most_two_totient_contributions
end A056777
