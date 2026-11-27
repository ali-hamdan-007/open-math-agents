import A056777CubePrimeAllFour
import A056777Squarefree
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma

namespace A056777FourFour

/-- The prime-factor shape with one square and two other distinct primes. -/
def RepeatedFour (n : ℕ) : Prop :=
  ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧ n = p^2*q*r

theorem RepeatedFour.not_squarefree {n : ℕ} (h : RepeatedFour n) : ¬Squarefree n := by
  obtain ⟨p,q,r,hp,_,_,_,_,_,rfl⟩ := h
  intro hsq
  exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hp) ⟨q*r,by ring⟩

private theorem squarefree_or_repeated {n m : ℕ}
    (hn : n.primeFactorsList.length = 4) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    Squarefree n ∨ RepeatedFour n := by
  rcases A056777CubeFour.four_factor_shape hn with ⟨k,hk⟩ | ⟨p,q,hp,hq,hpq,hn'⟩ |
    h | ⟨p,q,r,s,hp,hq,hr,hs,hpq,hpr,hps,hqr,hqs,hrs,hn'⟩
  · have hn0 : n ≠ 0 := by rintro rfl; simp at hn
    have hm0 : m ≠ 0 := by rintro rfl; simp at hm
    exfalso
    rcases hgap with he | he
    · have hstep : σ 1 (n+12)=σ 1 n+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).1 (Or.inl ⟨k,hk⟩)
    · have hstep : σ 1 (m+12)=σ 1 m+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hstep).2
        (Or.inl ⟨k,he.trans hk⟩)
  · exfalso
    rw [hn'] at hgap hφ hσ
    exact A056777.no_cube_prime_four_partner hp hq hpq hm hgap hφ hσ
  · exact Or.inr h
  · left
    rw [hn']
    have hc₁ := (Nat.coprime_primes hp hq).mpr hpq
    have hc₂ := ((Nat.coprime_primes hp hr).mpr hpr).mul_left
      ((Nat.coprime_primes hq hr).mpr hqr)
    have hc₃ := (((Nat.coprime_primes hp hs).mpr hps).mul_left
      ((Nat.coprime_primes hq hs).mpr hqs)).mul_left ((Nat.coprime_primes hr hs).mpr hrs)
    exact Nat.squarefree_mul_iff.mpr ⟨hc₃,Nat.squarefree_mul_iff.mpr
      ⟨hc₂,Nat.squarefree_mul_iff.mpr ⟨hc₁,hp.squarefree,hq.squarefree⟩,hr.squarefree⟩,
      hs.squarefree⟩

private theorem no_squarefree_squarefree {n : ℕ}
    (hn : n.primeFactorsList.length = 4) (h₁ : Squarefree n) (h₂ : Squarefree (n+12))
    (hφ : (n+12).totient=n.totient+12) (hσ : σ 1 (n+12)=σ 1 n+12) : False := by
  have hn' : 1 < n := by
    by_contra! h
    interval_cases n <;> simp at hn
  have hnnp : ¬n.Prime := by intro hp; simp [Nat.primeFactorsList_prime hp] at hn
  obtain ⟨p,hp,_,_,hp',he⟩ :=
    A056777Squarefree.prime_quadruple_of_squarefree_pair hn' hnnp h₁ h₂ hφ hσ
  have hh := (Nat.perm_primeFactorsList_mul hp.ne_zero hp'.ne_zero).length_eq
  rw [← he,Nat.primeFactorsList_prime hp,Nat.primeFactorsList_prime hp'] at hh
  simp [hn] at hh

/-- Both endpoints have one of the two stated factorization shapes, and at least one is
a square times two other distinct primes. This is the unrestricted 4×4 shape reduction. -/
theorem remaining_four_four_shapes {n m : ℕ}
    (hn : n.primeFactorsList.length = 4) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    (RepeatedFour n ∧ RepeatedFour m) ∨
      (RepeatedFour n ∧ Squarefree m) ∨ (Squarefree n ∧ RepeatedFour m) := by
  rcases squarefree_or_repeated hn hm hgap hφ hσ with hn' | hn' <;>
    rcases squarefree_or_repeated hm hn hgap.symm hφ.symm hσ.symm with hm' | hm'
  · exfalso
    rcases hgap with h | h
    · rw [← h] at hm' hφ hσ
      exact no_squarefree_squarefree hn hn' hm' (by omega) (by omega)
    · rw [← h] at hn' hφ hσ
      exact no_squarefree_squarefree hm hm' hn' (by omega) (by omega)
  · exact Or.inr (Or.inr ⟨hn',hm'⟩)
  · exact Or.inr (Or.inl ⟨hn',hm'⟩)
  · exact Or.inl ⟨hn',hm'⟩

end A056777FourFour

#print axioms A056777FourFour.remaining_four_four_shapes
