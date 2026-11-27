import A056777ThreeFourResidual
import A056777OddRepeatedFourDiscriminant

open scoped ArithmeticFunction.sigma

/-- The two A056777 jump conditions cannot hold between endpoints with exactly
three and four prime factors counted with multiplicity. Either endpoint can be smaller. -/
theorem A056777.no_three_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  obtain ⟨p,q,r,s,t,D,hp,hq,hr,hs,ht,hpq,hrs,hrt,hst,hn',hm',hop,hoq,hor,hos,hot,_⟩ :=
    A056777ThreeFourResidual.odd_repeated_residual hn hm hgap hφ hσ
  rw [hn',hm'] at hgap hφ hσ
  exact A056777OddRepeatedFourDiscriminant.no_odd_square_prime_square_two_primes_pair
    hp hq hr hs ht hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ

#print axioms A056777.no_three_four_pair
