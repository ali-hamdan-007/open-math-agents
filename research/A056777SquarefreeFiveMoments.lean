import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace A056777SquarefreeFiveMoments

private theorem pow_five_bounds (p q X Z : ℤ)
    (hp : 7≤p) (hq : 3≤q) (hX : 0≤X)
    (hXup : 2*X≤q+2*p+1) (hZ : p^2*q-12≤Z) (hcyc : Z^3≤X^5) : 64*p<q := by
  have hp0 : 0<p := by omega
  have hq0 : 0<q := by omega
  have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ)≤7) hp 2
  have hp4 := pow_le_pow_left₀ (by decide : (0:ℤ)≤7) hp 4
  have hpq : 147≤p^2*q := by
    have h := mul_le_mul hp2 hq (by decide : (0:ℤ)≤3) (sq_nonneg p)
    nlinarith only [h]
  have hZ0 : 0≤Z := by omega
  have hZ9 : 9*(p^2*q)≤10*Z := by omega
  have hcub := pow_le_pow_left₀ (show 0≤9*(p^2*q) by positivity) hZ9 3
  have hpScale := mul_le_mul_of_nonneg_right hp4 (show 0≤p^2*q^3 by positivity)
  by_contra! hq64
  by_cases hqP : q<p
  · have hX2 : X≤2*p := by omega
    have hx := pow_le_pow_left₀ hX hX2 5
    have hZ2 : 2*p^2≤Z := by
      have hh := mul_nonneg (sq_nonneg p) (show 0≤q-3 by omega)
      nlinarith only [hh,hZ,hp2]
    have hz := pow_le_pow_left₀ (show 0≤2*p^2 by positivity) hZ2 3
    have hh := mul_le_mul_of_nonneg_right hp (show 0≤p^5 by positivity)
    have hh' : 0<p^5 := by positivity
    nlinarith only [hx,hz,hh,hh',hcyc]
  by_cases hq4 : q≤4*p
  · have hX2 : X≤2*q := by omega
    have hx := pow_le_pow_left₀ hX hX2 5
    have hqle := pow_le_pow_left₀ hq0.le hq4 2
    have hh := mul_le_mul_of_nonneg_right hqle (show 0≤q^3 by positivity)
    have hpos : 0<p^2*q^3 := by positivity
    nlinarith only [hcub,hx,hh,hpScale,hcyc,hpos]
  · have hx4 : 5*X≤4*q := by omega
    have hx := pow_le_pow_left₀ (show 0≤5*X by positivity) hx4 5
    have hqle := pow_le_pow_left₀ hq0.le hq64 2
    have hh := mul_le_mul_of_nonneg_right hqle (show 0≤q^3 by positivity)
    have hpos : 0<p^2*q^3 := by positivity
    nlinarith only [hcub,hx,hh,hpScale,hcyc,hpos]

/-- The moment inequalities for a squarefree quintic cannot hold at the values
required by a repeated square-times-prime endpoint. -/
theorem moments_impossible (p q X A Y Z : ℤ)
    (hp : 7≤p) (hq : 3≤q) (hA : 0≤A) (hY : 0≤Y) (hX : 0≤X)
    (hK : 2*(X+A)=q+2*p+1)
    (hYup : 2*Y≤2*p^2+(2*p+1)*q+1)
    (hZ : p^2*q-12≤Z)
    (hcyc : Z^3≤X^5) (hXA : 30*A≤X) (hNew : 5*X*Z≤2*Y^2) : False := by
  have hp0 : 0<p := by omega
  have hq0 : 0<q := by omega
  have hq64 : 64*p<q := pow_five_bounds p q X Z hp hq hX (by omega) hZ hcyc
  have hY' : 11*Y≤12*p*q := by
    have hh := mul_nonneg (show 0≤2*p-11 by omega) (show 0≤q-64*p by omega)
    have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ)≤7) hp 2
    have h2 := mul_nonneg hp0.le (show 0≤p-7 by omega)
    nlinarith only [hh,hYup,h2,hp2]
  have hX' : 31*X≥15*q := by omega
  have hZ' : 100*Z≥99*p^2*q := by
    have hp2 := pow_le_pow_left₀ (by decide : (0:ℤ)≤7) hp 2
    have hq' : 448≤q := by omega
    have hh := mul_le_mul hp2 hq' (by decide : (0:ℤ)≤448) (sq_nonneg p)
    nlinarith only [hh,hZ]
  have hZ0 : 0≤Z := by
    have hh : 0≤99*p^2*q := by positivity
    omega
  have hXprod := mul_le_mul hX' hZ' (show 0≤99*p^2*q by positivity)
    (show 0≤31*X by positivity)
  have hYsq := pow_le_pow_left₀ (show 0≤11*Y by positivity) hY' 2
  have hpos : 0<p^2*q^2 := by positivity
  nlinarith only [hXprod,hYsq,hNew,hpos]

end A056777SquarefreeFiveMoments

#print axioms A056777SquarefreeFiveMoments.moments_impossible
