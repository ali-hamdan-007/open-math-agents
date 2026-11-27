import A056777CubePrimeFourFour
import A056777CubePrimeSquarefreeFour
import A056777CubeFour

open scoped ArithmeticFunction.sigma
open Nat

/-- The only remaining four-factor partner for p³q is r²st with three distinct
prime bases on the partner side. Either endpoint can be smaller. -/
theorem A056777.cube_prime_four_partner_shape {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hm : m.primeFactorsList.length = 4)
    (hgap : p^3*q+12=m ∨ m+12=p^3*q)
    (hφ : (p^3*q).totient+m=m.totient+p^3*q)
    (hσ : σ 1 (p^3*q)+m = σ 1 m+p^3*q) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
      r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ m = r^2*s*t := by
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨r,s,hr,hs,hrs,hm'⟩ |
    h | ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm'⟩
  · exfalso
    rcases hgap with he | he
    · have hste : σ 1 (p^3*q+12)=σ 1 (p^3*q)+12 := by rw [he]; omega
      have hn0 : p^3*q ≠ 0 := mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hste).2 (Or.inl ⟨k,he.trans hk⟩)
    · have hste : σ 1 (m+12)=σ 1 m+12 := by rw [he]; omega
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hste).1 (Or.inl ⟨k,hk⟩)
  · rw [hm'] at hgap hφ
    exact (A056777CubePrimeFourFour.no_cube_prime_cube_prime_gap_twelve hp hq hr hs
      hpq hrs hgap hφ).elim
  · exact h
  · rw [hm'] at hgap hφ hσ
    exact (A056777CubePrimeSquarefreeFour.no_cube_prime_squarefree_four_gap_twelve hp hq hr hs ht hu
      hpq hrs hrt hru hst hsu htu hgap hφ hσ).elim

#print axioms A056777.cube_prime_four_partner_shape
