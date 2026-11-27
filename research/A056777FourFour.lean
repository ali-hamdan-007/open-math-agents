import A056777EvenFourFour
import A056777OddFour
import Mathlib.Tactic.Ring

open scoped ArithmeticFunction.sigma

namespace A056777FourFour

private theorem repeated_distinct_count {n : ℕ} (h : RepeatedFour n) :
    3 ≤ n.primeFactors.card := by
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ := h
  have hz : p^2*q*r ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero) hr.ne_zero
  have hset : ({p,q,r} : Finset ℕ) ⊆ (p^2*q*r).primeFactors := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with h|h|h <;> subst a
    · exact Nat.mem_primeFactors.mpr ⟨hp,⟨p*q*r,by ring⟩,hz⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq,⟨p^2*r,by ring⟩,hz⟩
    · exact Nat.mem_primeFactors.mpr ⟨hr,⟨p^2*q,by ring⟩,hz⟩
  have hl := Finset.card_le_card hset
  simpa [hpq,hpr,hqr] using hl

private theorem squarefree_distinct_count {n : ℕ} (hn : n.primeFactorsList.length=4)
    (hs : Squarefree n) : 3 ≤ n.primeFactors.card := by
  rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hn]
  decide

/-- If both endpoints are odd and each has at least three distinct prime factors,
their totients cannot have a step of twelve when the arguments do. -/
theorem no_odd_three_distinct_pair {n m : ℕ} (hn : Odd n) (hm : Odd m)
    (hcn : 3 ≤ n.primeFactors.card) (hcm : 3 ≤ m.primeFactors.card)
    (hgap : n+12=m ∨ m+12=n) (hφ : n.totient+m=m.totient+n) : False := by
  have hnd : 8 ∣ n.totient :=
    (pow_dvd_pow 2 hcn).trans (A056777OddFour.two_pow_card_dvd_totient hn)
  have hmd : 8 ∣ m.totient :=
    (pow_dvd_pow 2 hcm).trans (A056777OddFour.two_pow_card_dvd_totient hm)
  omega

end A056777FourFour

/-- The A056777 jump conditions exclude every pair of endpoints with exactly
four prime factors each, counted with multiplicity. Either endpoint can be smaller. -/
theorem A056777.no_four_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  obtain ⟨ho,ho',hshape⟩ := A056777EvenFourFour.odd_four_four_residual hn hm hgap hφ hσ
  apply A056777FourFour.no_odd_three_distinct_pair ho ho' _ _ hgap hφ
  · rcases hshape with h|h|h
    · exact A056777FourFour.repeated_distinct_count h.1
    · exact A056777FourFour.repeated_distinct_count h.1
    · exact A056777FourFour.squarefree_distinct_count hn h.1
  · rcases hshape with h|h|h
    · exact A056777FourFour.repeated_distinct_count h.2
    · exact A056777FourFour.squarefree_distinct_count hm h.2
    · exact A056777FourFour.repeated_distinct_count h.2

#print axioms A056777FourFour.no_odd_three_distinct_pair
#print axioms A056777.no_four_four_pair
