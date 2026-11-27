import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

theorem square_prime_formulas {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p^2*q).totient + p*(p+q-1) = p^2*q ∧
    σ 1 (p^2*q) + (p^2*q).totient = 2*(p^2*q)+q+2*p+1 := by
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hφ : (p^2).totient=p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  have hσ : σ 1 (p^2)=1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hσq : σ 1 q=q+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hq
  rw [Nat.totient_mul hc,hφ,Nat.totient_prime hq,
    isMultiplicative_sigma.map_mul_of_coprime hc,hσ,hσq]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1]
  constructor <;> ring

private theorem no_repeated_moments (p q r s : ℤ)
    (hq : 3 ≤ q) (hr : 3 ≤ r) (hs : 3 ≤ s)
    (hop : p%2=1) (hor : r%2=1)
    (hK : s+2*r=q+2*p+4)
    (hF : p*(p+q-1)=r*(r+s-1)+6)
    (hG : r^2*s=p^2*q+6) : False := by
  let d := p-r
  have hp' : p=r+d := by dsimp [d]; ring
  have hs' : s=q+2*d+4 := by dsimp [d]; omega
  have hF' : d*(d+q-1)=4*r+6 := by
    rw [hp',hs'] at hF
    nlinarith only [hF]
  have hG' : r^2*(2*d+4)-(2*r*d+d^2)*q=6 := by
    rw [hp',hs'] at hG
    nlinarith only [hG]
  have hdpos : 0 < d := by
    by_contra! h
    have hn : 0 ≤ d+q-1 := by
      by_cases he : d=0
      · omega
      · have hd2 : d ≤ -2 := by dsimp [d] at *; omega
        omega
    have hneg := mul_nonpos_of_nonpos_of_nonneg h hn
    nlinarith only [hneg,hF',hr]
  have hd2 : 2 ≤ d := by dsimp [d] at *; omega
  have hpoly : d^3+2*d^2*r-d^2+2*d*r^2-6*d*r-6*d-4*r^2-12*r-6=0 := by
    linear_combination hG'+(2*r+d)*hF'
  by_cases hd : d=2
  · rw [hd] at hpoly
    nlinarith only [hpoly,hr]
  · let U := d-4
    let V := r-3
    have hU : 0 ≤ U := by
      dsimp [U,d] at *
      omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hpos : 0 < U^3+2*U^2*V+17*U^2+2*U*V^2+22*U*V+82*U+
        4*V^2+20*V+42 := by positivity
    have he : d^3+2*d^2*r-d^2+2*d*r^2-6*d*r-6*d-4*r^2-12*r-6 =
        U^3+2*U^2*V+17*U^2+2*U*V^2+22*U*V+82*U+4*V^2+20*V+42 := by
      dsimp [U,V]
      ring
    rw [← he,hpoly] at hpos
    omega

/-- After removing one factor of two, two repeated-prime length-three cores cannot
satisfy the shifted totient and divisor-sum equations. -/
theorem no_odd_repeated_cores {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s)
    (hg : p^2*q+6=r^2*s)
    (hφ : (r^2*s).totient=(p^2*q).totient+12)
    (hσ : σ 1 (r^2*s)=σ 1 (p^2*q)+4) : False := by
  have ⟨hFp,hKp⟩ := square_prime_formulas hp hq hpq
  have ⟨hFr,hKr⟩ := square_prime_formulas hr hs hrs
  have hK : s+2*r=q+2*p+4 := by omega
  have hF : p*(p+q-1)=r*(r+s-1)+6 := by omega
  have hq3 : 3 ≤ q := by have := hq.two_le; have := Nat.odd_iff.mp hoq; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; have := Nat.odd_iff.mp hor; omega
  have hs3 : 3 ≤ s := by have := hs.two_le; have := Nat.odd_iff.mp hos; omega
  have hpp := Nat.odd_iff.mp hop
  have hrr := Nat.odd_iff.mp hor
  have hpq1 : 1 ≤ p+q := by have := hp.pos; omega
  have hrs1 : 1 ≤ r+s := by omega
  zify [hpq1,hrs1] at hK hF hg hq3 hr3 hs3 hpp hrr
  exact no_repeated_moments p q r s hq3 hr3 hs3 hpp hrr hK hF hg.symm

end A056777EvenFourFour

#print axioms A056777EvenFourFour.no_odd_repeated_cores
