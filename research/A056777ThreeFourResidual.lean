import A056777ThreeFourShapes
import A056777EvenRepeatedFour
import A056777SquarePrimeCubePrime
import A056777OddRepeatedFour
import A056777OddRepeatedFourBound

open scoped ArithmeticFunction.sigma
open Nat

namespace A056777ThreeFourResidual

/-- Any three-versus-four A056777 pair must lie in the odd p²q/r²st class,
with the stated base bounds, residue conditions and signed prime-divisor sieve. -/
theorem odd_repeated_residual {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    ∃ (p q r s t : ℕ) (D : ℤ),
      p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ t.Prime ∧
      p ≠ q ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
      n = p^2*q ∧ m = r^2*s*t ∧
      Odd p ∧ Odd q ∧ Odd r ∧ Odd s ∧ Odd t ∧
      (D=12 ∨ D=-12) ∧ (m:ℤ)-(n:ℤ)=D ∧
      7 ≤ p ∧ p+4 ≤ r ∧ r < 8*p ∧
      p%4=3 ∧ q%8=3 ∧ (s*t)%8=7 ∧ (s+t)%8=0 ∧
      r<q ∧ s<q ∧ t<q ∧
      ((r:ℤ) ∣ (p:ℤ)^2*((p:ℤ)-1)-D) ∧
      (r:ℤ) ∣ ((r:ℤ)-p)^2*((r:ℤ)-p+1)+D := by
  obtain ⟨p,q,hp,hq,hpq,hndef,hfour⟩ :=
    A056777ThreeFourShapes.remaining_shapes_three_four_pair hn hm hgap hφ hσ
  rw [hndef] at hgap hφ hσ
  have hne : ¬ Even (p^2*q) := fun he =>
    A056777EvenRepeatedFour.no_even_repeated_three_four_pair hp hq hpq he hm hgap hφ hσ
  have ho := Nat.not_even_iff_odd.mp hne
  have hom : Odd m := by
    have hh := Nat.odd_iff.mp ho
    exact Nat.odd_iff.mpr (by omega)
  simp only [pow_two, Nat.odd_mul] at ho
  rcases hfour with ⟨r,s,hr,hs,hrs,hmdef⟩ | ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hmdef⟩
  · rw [hmdef] at hφ hσ
    exact (A056777SquarePrimeCubePrime.no_squarePrime_cubePrime hp hq hr hs hpq hrs hφ hσ).elim
  rw [hmdef] at hgap hφ hσ hom
  simp only [pow_two,Nat.odd_mul] at hom
  have hop := ho.1.1
  have hoq := ho.2
  have hor := hom.1.1.1
  have hos := hom.1.2
  have hot := hom.2
  obtain ⟨hsep,hp4,hq8,hst8,hsum8⟩ :=
    A056777OddRepeatedFour.odd_square_prime_square_two_primes_constraints hp hq hr hs ht hpq
      hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  have hp7 := A056777OddRepeatedFour.odd_square_prime_square_two_primes_seven_le hp hq hr hs ht
    hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  obtain ⟨hrq,hsq,htq⟩ :=
    A056777OddRepeatedFour.odd_square_prime_square_two_primes_largest hp hq hr hs ht hpq
      hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  let D : ℤ := (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q
  have hD : D = 12 ∨ D = -12 := by
    zify at hgap
    dsimp [D]
    simp only [mul_assoc] at hgap ⊢
    omega
  have h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q := ⟨rfl,hφ,hσ⟩
  have hrB := A056777OddRepeatedFour.repeated_prime_linear_bound D hp hq hr hs ht hpq
    hrs hrt hst hp7 hD h
  have hdvd := A056777OddRepeatedFour.prime_divisor_sieve D hp hq hr hs ht hpq hrs hrt hst h
  have hdd := A056777OddRepeatedFour.repeated_prime_distance_sieve D hdvd
  have hgD : (m:ℤ)-(n:ℤ)=D := by rw [hndef,hmdef]; push_cast; dsimp [D]; ring
  exact ⟨p,q,r,s,t,D,hp,hq,hr,hs,ht,hpq,hrs,hrt,hst,hndef,hmdef,hop,hoq,hor,hos,hot,
    hD,hgD,hp7,hsep,hrB,hp4,hq8,hst8,hsum8,hrq,hsq,htq,hdvd,hdd⟩

end A056777ThreeFourResidual

#print axioms A056777ThreeFourResidual.odd_repeated_residual
