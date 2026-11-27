import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubePrimeSquarefreeFour

private theorem fourth_newton (r s t u : ℤ) :
    8*(r*s+r*t+r*u+s*t+s*u+t*u)*(r*s*t*u) ≤
      3*(r*s*t+r*s*u+r*t*u+s*t*u)^2 := by
  let a := r*s*t
  let b := r*s*u
  let c := r*t*u
  let d := s*t*u
  have h : 8*(a*b+a*c+a*d+b*c+b*d+c*d) ≤ 3*(a+b+c+d)^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
      sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
  dsimp [a,b,c,d] at h
  nlinarith only [h]

private theorem middle_newton (r s t u : ℤ) :
    9*(r+s+t+u)*(r*s*t+r*s*u+r*t*u+s*t*u) ≤
      4*(r*s+r*t+r*u+s*t+s*u+t*u)^2 := by
  -- The shared-edge squares carry weight one, and the complementary ones weight four.
  nlinarith only [sq_nonneg (r*s-r*t),sq_nonneg (r*s-r*u),
    sq_nonneg (r*s-s*t),sq_nonneg (r*s-s*u),
    sq_nonneg (r*t-r*u),sq_nonneg (r*t-s*t),sq_nonneg (r*t-t*u),
    sq_nonneg (r*u-s*u),sq_nonneg (r*u-t*u),sq_nonneg (s*t-s*u),
    sq_nonneg (s*t-t*u),sq_nonneg (s*u-t*u),
    sq_nonneg (r*s-t*u),sq_nonneg (r*t-s*u),sq_nonneg (r*u-s*t)]

private theorem pair_cube_bound (r s t u : ℤ)
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (hu : 0 < u) :
    27*(r*s*t+r*s*u+r*t*u+s*t*u)^2 ≤
      2*(r*s+r*t+r*u+s*t+s*u+t*u)^3 := by
  let a := r+s+t+u
  let x := r*s+r*t+r*u+s*t+s*u+t*u
  let y := r*s*t+r*s*u+r*t*u+s*t*u
  have ha : 0 < a := by dsimp [a]; positivity
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have h₁ : 8*x ≤ 3*a^2 := by
    dsimp [x,a]
    nlinarith only [sq_nonneg (r-s),sq_nonneg (r-t),sq_nonneg (r-u),
      sq_nonneg (s-t),sq_nonneg (s-u),sq_nonneg (t-u)]
  have h₂ : 9*a*y ≤ 4*x^2 := middle_newton r s t u
  have h₂' := pow_le_pow_left₀ (show 0 ≤ 9*a*y by positivity) h₂ 2
  have h₁' := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ 27*y^2 by positivity)
  change 27*y^2 ≤ 2*x^3
  by_contra! h
  have h' := mul_pos (show 0 < 27*y^2-2*x^3 by omega) hx
  nlinarith only [h₂',h₁',h']

private theorem positive_newton_margin (p q : ℤ) (hp : 3 ≤ p) (hq : 4*p+1 ≤ q) :
    let L := (p+1)*(q+1)+2*p^2-2
    0 < 16*L*(p^3*q-12)-3*(2*p^2*(p+q-1)+L)^2 := by
  let a := p-3
  let b := q-4*p-1
  have ha : 0 ≤ a := by dsimp [a]; omega
  have hb : 0 ≤ b := by dsimp [b]; omega
  let P := 4*a^4+52*a^3+237*a^2+444*a+276
  let Q := 40*a^5+644*a^4+3976*a^3+11736*a^2+16188*a+7656
  let R := 84*a^6+1632*a^5+12768*a^4+51480*a^3+111168*a^2+116352*a+39636
  have hpos : 0 < P*b^2+Q*b+R := by dsimp [P,Q,R]; positivity
  dsimp only
  have he : 16*((p+1)*(q+1)+2*p^2-2)*(p^3*q-12)-
      3*(2*p^2*(p+q-1)+((p+1)*(q+1)+2*p^2-2))^2 = P*b^2+Q*b+R := by
    dsimp [P,Q,R,a,b]
    ring
  rw [he]
  exact hpos

private theorem inconsistent_moments (p q x y z : ℤ)
    (hp : 3 ≤ p) (hq : 2 ≤ q) (hx : 0 < x) (hy : 0 < y)
    (hX : 2*x=(p+1)*(q+1)+2*p^2-2)
    (hYlow : p^2*(p+q-1) ≤ y) (hYhigh : y ≤ p^2*(p+q-1)+x)
    (hZ : p^3*q-12 ≤ z)
    (hNewton : 8*x*z ≤ 3*y^2) (hMac : 27*y^2 ≤ 2*x^3) : False := by
  by_cases hqsmall : q ≤ 4*p
  · let S := p+q
    have hp0 : 0 ≤ p := by omega
    have hS : 5 ≤ S := by dsimp [S]; omega
    have hS5 : S ≤ 5*p := by dsimp [S]; omega
    have hxup : x ≤ p*S := by
      dsimp [S]
      have hh := mul_nonneg (show 0 ≤ p-1 by omega) (show 0 ≤ q-1 by omega)
      nlinarith only [hh,hX]
    have hx3 := pow_le_pow_left₀ hx.le hxup 3
    have hupper := mul_le_mul_of_nonneg_left hS5 (show 0 ≤ p^3*S^2 by positivity)
    have hSq : 4*S ≤ 5*(S-1) := by omega
    have hSq2 := pow_le_pow_left₀ (show 0 ≤ 4*S by omega) hSq 2
    have hmid := mul_le_mul_of_nonneg_left hSq2 (show 0 ≤ p^4 by positivity)
    have hy2 := pow_le_pow_left₀ (mul_nonneg (sq_nonneg p) (show 0 ≤ S-1 by omega)) hYlow 2
    nlinarith only [hx3,hupper,hmid,hy2,hMac,sq_pos_of_pos hy]
  · have hlarge : 4*p+1 ≤ q := by omega
    have h := positive_newton_margin p q hp hlarge
    dsimp only at h
    rw [← hX] at h
    have hZ' := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 8*x by omega)
    have hY' := pow_le_pow_left₀ hy.le hYhigh 2
    nlinarith only [h,hZ',hY',hNewton]

/-- Cube-times-prime and a squarefree product of four primes cannot be
twelve apart and satisfy both jump conditions. -/
theorem no_cube_prime_squarefree_four_gap_twelve {p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : p^3*q+12 = r*s*t*u ∨ r*s*t*u+12 = p^3*q)
    (hφ : (p^3*q).totient + r*s*t*u = (r*s*t*u).totient + p^3*q)
    (hσ : σ 1 (p^3*q) + r*s*t*u = σ 1 (r*s*t*u) + p^3*q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  by_cases hp2 : p = 2
  · subst p
    have hsq : Squarefree (r*s*t*u) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₃, Nat.squarefree_mul_iff.mpr
        ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁,hr.squarefree,hs.squarefree⟩,ht.squarefree⟩,
        hu.squarefree⟩
    have hdiv : 2*2 ∣ r*s*t*u := by norm_num at hgap ⊢; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσpp : σ 1 (p^3) = 1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hφpp : (p^3).totient = p^2*(p-1) := Nat.totient_prime_pow_succ hp 2
  rw [Nat.totient_mul hcp,hφpp,Nat.totient_prime hq,Nat.totient_mul hc₃,Nat.totient_mul hc₂,
    Nat.totient_mul hc₁,Nat.totient_prime hr,Nat.totient_prime hs,Nat.totient_prime ht,
    Nat.totient_prime hu] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp,hσpp,hσp hq,
    isMultiplicative_sigma.map_mul_of_coprime hc₃,isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,hσp hr,hσp hs,hσp ht,hσp hu] at hσ
  have hpr := hp.pos
  have hqr := hq.pos
  have hrr := hr.pos
  have hsr := hs.pos
  have htr := ht.pos
  have hur := hu.pos
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have ht2 := ht.two_le
  have hu2 := hu.two_le
  have hg : p^3*q ≤ r*s*t*u+12 := by omega
  zify [hpr,hqr,hrr,hsr,htr,hur] at hp3 hq2 hr2 hs2 ht2 hu2 hg hφ hσ
  let a : ℤ := r+s+t+u
  let x : ℤ := r*s+r*t+r*u+s*t+s*u+t*u
  let y : ℤ := r*s*t+r*s*u+r*t*u+s*t*u
  let z : ℤ := r*s*t*u
  have hX : 2*x=((p:ℤ)+1)*(q+1)+2*(p:ℤ)^2-2 := by dsimp [x]; nlinarith only [hφ,hσ]
  have hY : y=(p:ℤ)^2*(p+q-1)+x-a+1 := by dsimp [a,x,y]; nlinarith only [hφ]
  have ha1 : 1 ≤ a := by dsimp [a]; omega
  have hax : a ≤ x := by
    dsimp [a,x]
    have h₁ := mul_nonneg (show 0 ≤ (r:ℤ)-2 by omega) (show 0 ≤ (s:ℤ)-1 by omega)
    have h₂ := mul_nonneg (show 0 ≤ (t:ℤ)-2 by omega) (show 0 ≤ (u:ℤ)-1 by omega)
    have h₃ : 0 ≤ (r:ℤ)*t+(r:ℤ)*u+(s:ℤ)*t+(s:ℤ)*u := by positivity
    nlinarith only [h₁,h₂,h₃,hs2,hu2]
  have hx : 0 < x := by
    dsimp [x]
    have hrr' : (0:ℤ)<r := by omega
    have hss' : (0:ℤ)<s := by omega
    have htt' : (0:ℤ)<t := by omega
    have huu' : (0:ℤ)<u := by omega
    positivity
  have hy : 0 < y := by
    dsimp [y]
    have hrr' : (0:ℤ)<r := by omega
    have hss' : (0:ℤ)<s := by omega
    have htt' : (0:ℤ)<t := by omega
    have huu' : (0:ℤ)<u := by omega
    positivity
  exact inconsistent_moments p q x y z hp3 hq2 hx hy hX (by omega) (by omega)
    (by dsimp [z]; omega) (fourth_newton r s t u)
    (pair_cube_bound r s t u (by omega) (by omega) (by omega) (by omega))

end A056777CubePrimeSquarefreeFour

#print axioms A056777CubePrimeSquarefreeFour.no_cube_prime_squarefree_four_gap_twelve
