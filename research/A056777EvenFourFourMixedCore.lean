import A056777EvenFourFourCore
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

private theorem triple_formulas {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (r*s*t).totient+(r*s+r*t+s*t)+1=r*s*t+(r+s+t) ∧
    σ 1 (r*s*t)+(r*s*t).totient=2*(r*s*t)+2*(r+s+t) := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hσ {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
    simpa using sigma_one_apply_prime_pow (i:=1) hp
  rw [Nat.totient_mul hc₂,Nat.totient_mul hc₁,Nat.totient_prime hr,
    Nat.totient_prime hs,Nat.totient_prime ht,isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,hσ hr,hσ hs,hσ ht]
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hr1,hs1,ht1]
  constructor <;> ring

private theorem first_newton (r s t : ℤ) : 3*(r*s+r*t+s*t) ≤ (r+s+t)^2 := by
  nlinarith only [sq_nonneg (r-s),sq_nonneg (r-t),sq_nonneg (s-t)]

private theorem second_newton (r s t : ℤ) :
    3*(r+s+t)*(r*s*t) ≤ (r*s+r*t+s*t)^2 := by
  nlinarith only [sq_nonneg (r*s-r*t),sq_nonneg (r*s-s*t),sq_nonneg (r*t-s*t)]

private theorem large_margin_plus (p S : ℤ) (hp : 11 ≤ p) (hS : 5*p+4 ≤ S) :
    0 < 3*S*(p^2*(2*S-2*p-1-4*(1))+6*(1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(1))^2 := by
  let U := p-11
  let V := S-5*p-4
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let P := 39*U^4+18*U^3*V^1+1731*U^3+2*U^2*V^2+581*U^2*V^1+28850*U^2+40*U^1*V^2+6246*U^1*V^1+214115*U^1+197*V^2+22387*V^1+597440
  have hpos : 0 < P := by dsimp [P]; positivity
  have he : 3*S*(p^2*(2*S-2*p-1-4*(1))+6*(1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(1))^2 = P := by
    dsimp [P,U,V]
    ring
  rw [he]
  exact hpos

private theorem large_margin_minus (p S : ℤ) (hp : 11 ≤ p) (hS : 5*p+4 ≤ S) :
    0 < 3*S*(p^2*(2*S-2*p-1-4*(-1))+6*(-1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(-1))^2 := by
  let U := p-11
  let V := S-5*p-4
  have hU : 0 ≤ U := by dsimp [U]; omega
  have hV : 0 ≤ V := by dsimp [V]; omega
  let P := 39*U^4+18*U^3*V^1+1707*U^3+2*U^2*V^2+573*U^2*V^1+27762*U^2+40*U^1*V^2+6006*U^1*V^1+198399*U^1+197*V^2+20655*V^1+524052
  have hpos : 0 < P := by dsimp [P]; positivity
  have he : 3*S*(p^2*(2*S-2*p-1-4*(-1))+6*(-1))-
      ((2*p+1)*S-(p+1)^2-(4*p+6)*(-1))^2 = P := by
    dsimp [P,U,V]
    ring
  rw [he]
  exact hpos

private theorem shifted_moments_impossible (p q S x z e : ℤ)
    (hq : 3 ≤ q) (hS : 15 ≤ S) (hp : p=5 ∨ p=7 ∨ 11≤p) (he : e=1 ∨ e=-1)
    (hQ : q=2*S-2*p-1-4*e)
    (hX : x=(2*p+1)*S-(p+1)^2-(4*p+6)*e)
    (hZ : z=p^2*q+6*e)
    (hN₁ : 3*x≤S^2) (hN₂ : 3*S*z≤x^2) : False := by
  have hZ' : z=p^2*(2*S-2*p-1-4*e)+6*e := by rw [hZ,hQ]
  rw [hX] at hN₁ hN₂
  rw [hZ'] at hN₂
  rcases hp with rfl | rfl | hp
  · have hS26 : 26≤S := by
      by_contra! h
      have hh := mul_nonneg (show 0≤S-15 by omega) (show 0≤25-S by omega)
      rcases he with rfl|rfl <;> nlinarith only [hh,hN₁,h]
    have hn := mul_nonneg (show 0≤S-26 by omega) (show 0≤29*S+431 by omega)
    rcases he with rfl|rfl <;> nlinarith only [hn,hN₂,hS26]
  · have hS38 : 38≤S := by
      by_contra! h
      have hh := mul_nonneg (show 0≤S-15 by omega) (show 0≤37-S by omega)
      rcases he with rfl|rfl <;> nlinarith only [hh,hN₁,h]
    have hn := mul_nonneg (show 0≤S-38 by omega) (show 0≤69*S+1887 by omega)
    rcases he with rfl|rfl <;> nlinarith only [hn,hN₂,hS38]
  · have hS' : 5*p+4 ≤ S := by
      by_contra! h
      let w := 2*(S-p)
      have hw : 0≤w := by dsimp [w]; rcases he with rfl|rfl <;> omega
      have hh := mul_nonneg hw (show 0≤8*p+6-w by dsimp [w]; omega)
      have hpp := mul_nonneg (show 0≤p-11 by omega) (show 0≤8*p+28 by omega)
      dsimp [w] at hh
      rcases he with rfl|rfl <;> nlinarith only [hh,hpp,hN₁,hp]
    rcases he with rfl|rfl
    · have hh := large_margin_plus p S hp hS'
      linarith only [hh,hN₂]
    · have hh := large_margin_minus p S hp hS'
      linarith only [hh,hN₂]

private theorem three_core_pair_impossible {q s t : ℕ}
    (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hq3 : q ≠ 3) (hs3 : s ≠ 3) (ht3 : t ≠ 3) (hst : s ≠ t)
    (hos : Odd s) (hot : Odd t)
    (h : ((3^2*q+6=3*(s*t)) ∧ (3*(s*t)).totient=(3^2*q).totient+12) ∨
      ((3*(s*t)+6=3^2*q) ∧ (3^2*q).totient=(3*(s*t)).totient+12)) : False := by
  have hprime := Nat.prime_three
  have hcq := ((Nat.coprime_primes hprime hq).mpr hq3.symm).pow_left 2
  have hcst := (Nat.coprime_primes hs ht).mpr hst
  have hc := ((Nat.coprime_primes hprime hs).mpr hs3.symm).mul_right
    ((Nat.coprime_primes hprime ht).mpr ht3.symm)
  rw [Nat.totient_mul hcq,Nat.totient_mul hc,Nat.totient_mul hcst,
    show ((3:ℕ)^2).totient=6 by decide,Nat.totient_prime hprime,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at h
  have hq1 := hq.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  have hs5 : 5≤s := by have := hs.two_le; have := Nat.odd_iff.mp hos; omega
  have ht5 : 5≤t := by have := ht.two_le; have := Nat.odd_iff.mp hot; omega
  zify [hq1,hs1,ht1] at h hs5 ht5
  norm_num at h
  rcases h with ⟨hg,hφ⟩ | ⟨hg,hφ⟩ <;> nlinarith only [hg,hφ,hs5,ht5]

/-- A repeated-prime odd core and a squarefree odd core cannot have the step of six
with totient step twelve and divisor-sum step four induced by dividing even endpoints by two. -/
theorem no_odd_mixed_cores {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hstep : (p^2*q+6=r*s*t ∧ (r*s*t).totient=(p^2*q).totient+12 ∧
      σ 1 (r*s*t)=σ 1 (p^2*q)+4) ∨
      (r*s*t+6=p^2*q ∧ (p^2*q).totient=(r*s*t).totient+12 ∧
      σ 1 (p^2*q)=σ 1 (r*s*t)+4)) : False := by
  by_cases hp3 : p=3
  · subst p
    have hg := hstep.imp And.left And.left
    have hd : 3 ∣ r*s*t := by norm_num at hg; omega
    simp only [Nat.prime_three.dvd_mul] at hd
    have eq_three {a : ℕ} (ha : a.Prime) (h : 3 ∣ a) : a=3 := by
      rcases (Nat.dvd_prime ha).mp h with h | h
      · omega
      · exact h.symm
    rcases hd with (hd|hd)|hd
    · obtain rfl := eq_three hr hd
      rw [show 3*s*t=3*(s*t) by ring] at hstep
      exact three_core_pair_impossible hq hs ht hpq.symm hrs.symm hrt.symm hst hos hot
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
    · obtain rfl := eq_three hs hd
      rw [show r*3*t=3*(r*t) by ring] at hstep
      exact three_core_pair_impossible hq hr ht hpq.symm hrs hst.symm hrt hor hot
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
    · obtain rfl := eq_three ht hd
      rw [show r*s*3=3*(r*s) by ring] at hstep
      exact three_core_pair_impossible hq hr hs hpq.symm hrt hst hrs hor hos
        (hstep.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩))
  have hpclass : p=5 ∨ p=7 ∨ 11≤p := by
    have hp2 := hp.two_le
    have hpo := Nat.odd_iff.mp hop
    have hp9 : p ≠ 9 := fun he => (by decide : ¬Nat.Prime 9) (he ▸ hp)
    omega
  have hq3 : 3≤q := by have := hq.two_le; have := Nat.odd_iff.mp hoq; omega
  have hS : 15≤r+s+t := by
    have := hr.two_le
    have := hs.two_le
    have := ht.two_le
    have := Nat.odd_iff.mp hor
    have := Nat.odd_iff.mp hos
    have := Nat.odd_iff.mp hot
    omega
  have ⟨hF,hK⟩ := square_prime_formulas hp hq hpq
  have ⟨hF',hK'⟩ := triple_formulas hr hs ht hrs hrt hst
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hpq1 : 1 ≤ p+q := by omega
  zify [hp1,hq1,hpq1] at hpclass hq3 hS hF hK hF' hK' hstep
  let S : ℤ := r+s+t
  let x : ℤ := r*s+r*t+s*t
  let z : ℤ := r*s*t
  have hN₁ : 3*x≤S^2 := first_newton r s t
  have hN₂ : 3*S*z≤x^2 := second_newton r s t
  rcases hstep with ⟨hg,hφ,hσ⟩|⟨hg,hφ,hσ⟩
  · have he : (1:ℤ)=1 ∨ (1:ℤ)=-1 := Or.inl rfl
    exact shifted_moments_impossible p q S x z 1 hq3 hS hpclass he
      (by dsimp [S]; omega) (by dsimp [x,S]; nlinarith only [hF,hK,hF',hK',hg,hφ,hσ])
      (by dsimp [z]; omega) hN₁ hN₂
  · have he : (-1:ℤ)=1 ∨ (-1:ℤ)=-1 := Or.inr rfl
    exact shifted_moments_impossible p q S x z (-1) hq3 hS hpclass he
      (by dsimp [S]; omega) (by dsimp [x,S]; nlinarith only [hF,hK,hF',hK',hg,hφ,hσ])
      (by dsimp [z]; omega) hN₁ hN₂

end A056777EvenFourFour

#print axioms A056777EvenFourFour.no_odd_mixed_cores
