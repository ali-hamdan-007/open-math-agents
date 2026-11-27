import A056777RepeatedTriple
import A056777RepeatedPrime

open scoped ArithmeticFunction.sigma

namespace A056777RepeatedTriple

/-- The simultaneous jumps by twelve cannot occur when both endpoints are nonsquarefree
and each has three prime factors counted with multiplicity. -/
theorem no_pair_of_nonsquarefree_length_three {n : ℕ}
    (hlen₁ : n.primeFactorsList.length = 3)
    (hlen₂ : (n + 12).primeFactorsList.length = 3)
    (hns₁ : ¬ Squarefree n) (hns₂ : ¬ Squarefree (n + 12))
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12) : False := by
  obtain ⟨p, q, r, s, hp, hq, hr, hs', hpq, hrs, hn, hm⟩ :=
    distinct_repeated_endpoints_of_totient_step hlen₁ hlen₂ hns₁ hns₂ ht
  have hprod : r ^ 2 * s = p ^ 2 * q + 12 := by rw [← hm, ← hn]
  have htot : (r ^ 2 * s).totient = (p ^ 2 * q).totient + 12 := by
    rw [← hm, ← hn]
    exact ht
  have hσ : σ 1 (r ^ 2 * s) = σ 1 (p ^ 2 * q) + 12 := by
    rw [← hm, ← hn]
    exact hs
  exact A056777.no_positive_gap_prime_sq_mul_prime hp hq hr hs' hpq hrs (by decide) hprod htot hσ

end A056777RepeatedTriple

#print axioms A056777RepeatedTriple.no_pair_of_nonsquarefree_length_three
