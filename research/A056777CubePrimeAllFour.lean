import A056777CubePrimeFourPartner
import A056777CubePrimeRepeatedFour

open scoped ArithmeticFunction.sigma

/-- A cube-times-prime endpoint cannot satisfy the A056777 jump conditions
with any endpoint having exactly four prime factors counted with multiplicity.
Either endpoint can be smaller. -/
theorem A056777.no_cube_prime_four_partner {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hm : m.primeFactorsList.length = 4)
    (hgap : p^3*q+12=m ∨ m+12=p^3*q)
    (hφ : (p^3*q).totient+m=m.totient+p^3*q)
    (hσ : σ 1 (p^3*q)+m=σ 1 m+p^3*q) : False := by
  obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hm'⟩ :=
    A056777.cube_prime_four_partner_shape hp hq hpq hm hgap hφ hσ
  rw [hm'] at hgap hφ hσ
  exact A056777CubePrimeRepeatedFour.no_cube_prime_square_two_primes_gap_twelve
    hp hq hr hs ht hpq hrs hrt hst hgap hφ hσ

#print axioms A056777.no_cube_prime_four_partner
