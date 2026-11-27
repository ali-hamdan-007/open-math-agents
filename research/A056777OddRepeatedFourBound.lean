import A056777OddRepeatedFour

open scoped ArithmeticFunction.sigma
open Nat

namespace A056777OddRepeatedFour

private theorem linear_bound_from_moments (p r A B D k : ℤ)
    (hp : 7 ≤ p) (hA0 : 0 ≤ A) (hD : D=12 ∨ D=-12)
    (hk : p^2*(p-1)-D=r*k)
    (hA : (r^2-(p+1)*r-2*p)*(A-(2*p+1))=(2*p^2+4*p)*r+3*p^2+k)
    (hB : (r^2-p^2)*B=p^2*((2*r+1)*A+2*r^2-2*p)+D)
    (hdisc : 4*B ≤ A^2) :
    r < 8*p := by
  by_contra! hr
  have hp0 : 0 < p := by omega
  have hr0 : 0 < r := by omega
  have hp2 : 49 ≤ p^2 := by
    have hh := mul_le_mul hp hp (by decide : (0:ℤ) ≤ 7) hp0.le
    nlinarith only [hh]
  have hk' : k ≤ p^2 := by
    by_contra! h
    have hh := mul_pos (show 0 < k-p^2 by omega) hr0
    have hh' := mul_nonneg (sq_nonneg p) (show 0 ≤ r-p by omega)
    have hD' : -12 ≤ D := by omega
    nlinarith only [hh,hh',hk,hD',hp2]
  have hDet : 3*r^2 ≤ 4*(r^2-(p+1)*r-2*p) := by
    have hh := mul_nonneg hr0.le (show 0 ≤ r-8*p by omega)
    have hh' := mul_nonneg hr0.le (show 0 ≤ p-2 by omega)
    nlinarith only [hh,hh',hr,hp]
  have hTop : (2*p^2+4*p)*r+3*p^2+k ≤ 3*p^2*r := by
    have hh := mul_nonneg (mul_nonneg hp0.le (show 0 ≤ p-5 by omega)) hr0.le
    have hh' := mul_nonneg hp0.le (show 0 ≤ r-4*p by omega)
    nlinarith only [hh,hh',hk']
  have hA' : 3*A ≤ 8*p := by
    have hX : 2*(A-(2*p+1)) ≤ p := by
      by_contra! hh
      have hx : 0 ≤ A-(2*p+1) := by omega
      have hlow := mul_le_mul_of_nonneg_right hDet hx
      have hh' := mul_pos (show 0 < 2*(A-(2*p+1))-p by omega) hr0
      have hh'' := mul_nonneg hp0.le (show 0 ≤ r-8*p by omega)
      have hm : 0 < r*(A-(2*p+1))-4*p^2 := by nlinarith only [hh',hh'']
      have hm' := mul_pos hm hr0
      nlinarith only [hlow,hA,hTop,hm']
    omega
  have hB' : 2*p^2 ≤ B := by
    by_contra! hh
    have hcoeff : 0 < r^2-p^2 := by
      have hpos := mul_pos (show 0 < r-p by omega) (show 0 < r+p by omega)
      nlinarith only [hpos]
    have hmul := mul_pos hcoeff (show 0 < 2*p^2-B by omega)
    have hnA := mul_nonneg (sq_nonneg p) (mul_nonneg (show 0 ≤ 2*r+1 by omega) hA0)
    have hpp := mul_nonneg (sq_nonneg p) (show 0 ≤ 2*p^2-2*p-2 by
      have hn := mul_nonneg hp0.le (show 0 ≤ p-2 by omega)
      nlinarith only [hn,hp])
    have hD' : -12 ≤ D := by omega
    nlinarith only [hmul,hnA,hpp,hB,hD',hp2]
  have hsq := mul_le_mul hA' hA' (by omega : 0 ≤ 3*A) (by omega : 0 ≤ 8*p)
  nlinarith only [hsq,hdisc,hB',hp2]

/-- The larger repeated prime in the final odd class is strictly below eight times
the smaller repeated prime. This uses the discriminant inequality for s,t. -/
theorem repeated_prime_linear_bound {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hp7 : 7 ≤ p) (hD : D=12 ∨ D=-12)
    (h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    r < 8*p := by
  obtain ⟨k,hk⟩ := prime_divisor_sieve D hp hq hr hs ht hpq hrs hrt hst h
  have hA := compact_sum_criterion D k hp hq hr hs ht hpq hrs hrt hst hk h
  have hB := ((moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h).2.2
  have hdisc : 4*((s:ℤ)*t) ≤ ((s:ℤ)+t)^2 := by nlinarith [sq_nonneg ((s:ℤ)-t)]
  have hbound := linear_bound_from_moments p r ((s:ℤ)+t) ((s:ℤ)*t) D k
    (by exact_mod_cast hp7) (by positivity) hD hk hA hB hdisc
  exact_mod_cast hbound

end A056777OddRepeatedFour

#print axioms A056777OddRepeatedFour.repeated_prime_linear_bound
