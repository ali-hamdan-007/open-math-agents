import A056777MixedFour
import A056777CubeFour
import A056777RepeatedTriple
import A056777Squarefree
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma
open Nat

namespace A056777MixedFour

private theorem four_distinct_primes {m : ℕ} (hl : m.primeFactorsList.length = 4)
    (hs : Squarefree m) : ∃ r s t u, r.Prime ∧ s.Prime ∧ t.Prime ∧ u.Prime ∧
      r ≠ s ∧ r ≠ t ∧ r ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ m = r*s*t*u := by
  rcases A056777CubeFour.four_factor_shape hl with ⟨k,hk⟩ | ⟨r,s,hr,hsp,hne,hm⟩ |
    ⟨r,s,t,hr,hsp,ht,hrs,hrt,hst,hm⟩ | h
  · have hk1 : k = 1 := by
      have hdiv : k*k ∣ m := by rw [hk, pow_two]
      exact Nat.isUnit_iff.mp (hs k hdiv)
    subst k
    simp [hk] at hl
  · have hd : r*r ∣ m := ⟨r*s, by rw [hm]; ring⟩
    exact ((Nat.squarefree_iff_prime_squarefree.mp hs _ hr) hd).elim
  · have hd : r*r ∣ m := ⟨s*t, by rw [hm]; ring⟩
    exact ((Nat.squarefree_iff_prime_squarefree.mp hs _ hr) hd).elim
  · exact h

private theorem composite_of_length_ge_three {n : ℕ} (h : 3 ≤ n.primeFactorsList.length) :
    1 < n ∧ ¬n.Prime := by
  constructor
  · by_contra! hle
    interval_cases n <;> simp at h
  · intro hp
    simp [Nat.primeFactorsList_prime hp] at h

private theorem not_quadruple_of_length_ge_three {n : ℕ} (h : 3 ≤ n.primeFactorsList.length)
    (hp : ∃ p : ℕ, p.Prime ∧ (p+2).Prime ∧ (p+6).Prime ∧ (p+8).Prime ∧ n = p*(p+8)) :
    False := by
  obtain ⟨p,hp,_,_,hp',hn⟩ := hp
  have hh := (Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero).length_eq
  rw [← hn, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hp'] at hh
  simp [hh] at h

/-- The two arithmetic jumps cannot occur between a three-factor endpoint and a squarefree
four-factor endpoint, regardless of which one is smaller or which primes are repeated. -/
theorem no_length_three_squarefree_length_four_pair {n m : ℕ}
    (h₁ : n.primeFactorsList.length = 3) (h₂ : m.primeFactorsList.length = 4)
    (hsf : Squarefree m) (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  by_cases hsf' : Squarefree n
  · rcases hgap with h | h
    · subst m
      obtain ⟨hn, hnp⟩ := composite_of_length_ge_three (by omega : 3 ≤ n.primeFactorsList.length)
      exact not_quadruple_of_length_ge_three (by omega : 3 ≤ n.primeFactorsList.length)
        (A056777Squarefree.prime_quadruple_of_squarefree_pair hn hnp hsf' hsf (by omega) (by omega))
    · subst n
      obtain ⟨hm, hmp⟩ := composite_of_length_ge_three (by omega : 3 ≤ m.primeFactorsList.length)
      exact not_quadruple_of_length_ge_three (by omega : 3 ≤ m.primeFactorsList.length)
        (A056777Squarefree.prime_quadruple_of_squarefree_pair hm hmp hsf hsf' (by omega) (by omega))
  · obtain ⟨p,q,hp,hq,rfl⟩ :=
      A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three h₁ hsf'
    by_cases he : p = q
    · subst q
      rw [← pow_succ] at hgap hφ hσ
      exact A056777CubeFour.no_cube_four_pair hp h₂ hgap hφ hσ
    · obtain ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,rfl⟩ := four_distinct_primes h₂ hsf
      exact no_mixed_four_gap_twelve hp hq hr hs ht hu he hrs hrt hru hst hsu htu hgap hφ hσ

end A056777MixedFour

#print axioms A056777MixedFour.no_length_three_squarefree_length_four_pair
