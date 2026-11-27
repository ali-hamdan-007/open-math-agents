import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777MixedFour

private theorem comp_pair_square_bound (r s t u : ℤ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    36 * (r*s*t*u) ≤ (r*s+r*t+r*u+s*t+s*u+t*u)^2 := by
  have hpair (a b c d : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
      4*(a*b*c*d) ≤ (a*b+c*d)*(a*c+b*d) := by
    nlinarith only [mul_nonneg (mul_nonneg hb hc) (sq_nonneg (a-d)),
      mul_nonneg (mul_nonneg ha hd) (sq_nonneg (b-c))]
  have h₁ := hpair r s t u hr hs ht hu
  have h₂ := hpair r s u t hr hs hu ht
  have h₃ := hpair r t u s hr ht hu hs
  nlinarith only [h₁,h₂,h₃,sq_nonneg (r*s-t*u),sq_nonneg (r*t-s*u),sq_nonneg (r*u-s*t)]

private theorem newton_four (r s t u : ℤ) :
    8 * (r*s+r*t+r*u+s*t+s*u+t*u) * (r*s*t*u) ≤
    3 * (r*s*t+r*s*u+r*t*u+s*t*u)^2 := by
  let a := r*s*t
  let b := r*s*u
  let c := r*t*u
  let d := s*t*u
  have h : 8*(a*b+a*c+a*d+b*c+b*d+c*d) ≤ 3*(a+b+c+d)^2 := by
    nlinarith only [sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (a-d),
      sq_nonneg (b-c),sq_nonneg (b-d),sq_nonneg (c-d)]
  dsimp [a,b,c,d] at h
  nlinarith only [h]

private theorem inconsistent_bounds (p q x y z : ℤ)
    (hp : 5 ≤ p) (hq : 2 ≤ q) (hx : 0 < x) (hy : 0 ≤ y)
    (hqx : q = 2*x-2*p+1) (hE : y ≤ (2*p+1)*x)
    (hprod : p^2*q - 12 ≤ z)
    (hA : 36*z ≤ x^2) (hN : 8*x*z ≤ 3*y^2) : False := by
  have hp0 : 0 ≤ p := by omega
  have hp2 : 25 ≤ p^2 := by
    have hh := mul_le_mul hp hp (by decide : (0:ℤ) ≤ 5) hp0
    nlinarith only [hh]
  have hx3 : 3*p < x := by
    by_contra! hx3
    have hsq := mul_le_mul hx3 hx3 hx.le (by omega : 0 ≤ 3*p)
    have hq2 := mul_le_mul_of_nonneg_left hq (sq_nonneg p)
    nlinarith only [hprod,hA,hsq,hq2,hp2]
  have hlo : 4*p^2*x ≤ 3*z := by
    have hh := mul_nonneg (sq_nonneg p) (show 0 ≤ 2*x-6*p by omega)
    have hq' := congrArg (fun u : ℤ => p^2*u) hqx
    nlinarith only [hprod,hh,hq',hp2]
  have hx48 : 48*p^2 ≤ x := by
    by_contra! hh
    have hn := mul_pos (show 0 < 48*p^2 - x by omega) hx
    nlinarith only [hA,hlo,hn]
  have hx16 : 16*p ≤ x := by
    have hh := mul_nonneg hp0 (show 0 ≤ p-1 by omega)
    nlinarith only [hx48,hh,hp0]
  have hstrong : 15*p^2*x ≤ 8*z := by
    have hh := mul_nonneg (sq_nonneg p) (show 0 ≤ x-16*p by omega)
    have hq' := congrArg (fun u : ℤ => p^2*u) hqx
    nlinarith only [hprod,hh,hq',hp2]
  have hysq := mul_le_mul hE hE hy
    (mul_nonneg (show 0 ≤ 2*p+1 by omega) hx.le)
  have hstrong' := mul_le_mul_of_nonneg_right hstrong hx.le
  have hcoeff : 3*(2*p+1)^2 < 15*p^2 := by
    have hh := mul_nonneg hp0 (show 0 ≤ p-5 by omega)
    nlinarith only [hh,hp,hp2]
  have hs := mul_lt_mul_of_pos_right hcoeff (mul_pos hx hx : 0 < x*x)
  nlinarith only [hs,hN,hysq,hstrong']

private theorem three_core_impossible {q r s t : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hr3 : r ≠ 3) (hs3 : s ≠ 3) (ht3 : t ≠ 3)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : 3^2*q + 12 = 3*(r*s*t) ∨ 3*(r*s*t) + 12 = 3^2*q)
    (hφ : (3^2*q).totient + 3*(r*s*t) = (3*(r*s*t)).totient + 3^2*q) : False := by
  have h3 := Nat.prime_three
  have hcop := ((Nat.coprime_primes h3 hq).mpr hq3.symm).pow_left 2
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes h3 hr).mpr hr3.symm).mul_right
    ((Nat.coprime_primes h3 hs).mpr hs3.symm)).mul_right ((Nat.coprime_primes h3 ht).mpr ht3.symm)
  rw [Nat.totient_mul hcop, Nat.totient_mul hc₃, Nat.totient_prime hq,
    show ((3 : ℕ)^2).totient = 6 by decide, Nat.totient_prime h3] at hφ
  norm_num at hφ hgap
  have hcl : r*s*t - (r*s*t).totient ≤ 5 := by
    have hq₂ := hq.two_le
    omega
  have hrp : 1 ≤ r := hr.pos
  have hsp : 1 ≤ s := hs.pos
  have htp : 1 ≤ t := ht.pos
  have hbound : (r*s*t).totient + s*t ≤ r*s*t := by
    rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_prime hr,
      Nat.totient_prime hs, Nat.totient_prime ht]
    have hh := Nat.mul_le_mul (Nat.mul_le_mul (le_refl (r-1)) (Nat.sub_le s 1)) (Nat.sub_le t 1)
    zify [hrp,hsp,htp] at hh ⊢
    nlinarith only [hh]
  have hs₂ := hs.two_le
  have ht₂ := ht.two_le
  have hst_big : 6 ≤ s*t := by
    by_cases hs₂' : s = 2
    · subst s
      have ht₃ : 3 ≤ t := by omega
      exact Nat.mul_le_mul (le_refl 2) ht₃
    · have hs₃ : 3 ≤ s := by omega
      exact Nat.mul_le_mul hs₃ ht₂
  omega

private theorem no_three_squarefree_four {q r s t u : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : 3^2*q + 12 = r*s*t*u ∨ r*s*t*u + 12 = 3^2*q)
    (hφ : (3^2*q).totient + r*s*t*u = (r*s*t*u).totient + 3^2*q) : False := by
  have hd : 3 ∣ r*s*t*u := by omega
  simp only [Nat.prime_three.dvd_mul] at hd
  have from_dvd (v : ℕ) (hv : v.Prime) (h : 3 ∣ v) : v = 3 := by
    rcases (Nat.dvd_prime hv).mp h with h | h
    · omega
    · exact h.symm
  rcases hd with ((hd | hd) | hd) | hd
  · obtain rfl := from_dvd r hr hd
    have hh : 3*s*t*u = 3*(s*t*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hs ht hu hrs.symm hrt.symm hru.symm hst hsu htu hgap hφ
  · obtain rfl := from_dvd s hs hd
    have hh : r*3*t*u = 3*(r*t*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr ht hu hrs hst.symm hsu.symm hrt hru htu hgap hφ
  · obtain rfl := from_dvd t ht hd
    have hh : r*s*3*u = 3*(r*s*u) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr hs hu hrt hst htu.symm hrs hru hsu hgap hφ
  · obtain rfl := from_dvd u hu hd
    have hh : r*s*t*3 = 3*(r*s*t) := by ring
    rw [hh] at hgap hφ
    exact three_core_impossible hq hq3 hr hs ht hru hsu htu hrs hrt hst hgap hφ

/-- A product of a prime square and a different prime cannot satisfy the simultaneous
A056777 shifts with a product of four distinct primes. Both orientations are covered. -/
theorem no_mixed_four_gap_twelve {p q r s t u : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime) (hu : u.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t)
    (hsu : s ≠ u) (htu : t ≠ u)
    (hgap : p^2*q + 12 = r*s*t*u ∨ r*s*t*u + 12 = p^2*q)
    (hφ : (p^2*q).totient + r*s*t*u = (r*s*t*u).totient + p^2*q)
    (hσ : σ 1 (p^2*q) + r*s*t*u = σ 1 (r*s*t*u) + p^2*q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  by_cases hp2 : p = 2
  · subst p
    have hsq : Squarefree (r*s*t*u) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₃, Nat.squarefree_mul_iff.mpr
        ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁, hr.squarefree, hs.squarefree⟩, ht.squarefree⟩,
        hu.squarefree⟩
    have hdiv : 2*2 ∣ r*s*t*u := by norm_num at hgap ⊢; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  by_cases hp3 : p = 3
  · subst p
    exact no_three_squarefree_four hq hpq.symm hr hs ht hu hrs hrt hru hst hsu htu hgap hφ
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
    have := hp.two_le
    omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσpp : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hφpp : (p^2).totient = p*(p-1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
  rw [Nat.totient_mul hcp, hφpp, Nat.totient_prime hq, Nat.totient_mul hc₃, Nat.totient_mul hc₂,
    Nat.totient_mul hc₁, Nat.totient_prime hr, Nat.totient_prime hs, Nat.totient_prime ht,
    Nat.totient_prime hu] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp, hσpp, hσp hq,
    isMultiplicative_sigma.map_mul_of_coprime hc₃, isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁, hσp hr, hσp hs, hσp ht, hσp hu] at hσ
  have hpr := hp.pos
  have hqr := hq.pos
  have hrr := hr.pos
  have hsr := hs.pos
  have htr := ht.pos
  have hur := hu.pos
  have hq2 := hq.two_le
  have hgap' : p^2*q ≤ r*s*t*u+12 := by omega
  zify [hpr,hqr,hrr,hsr,htr,hur] at hp5 hq2 hgap' hφ hσ
  let x : ℤ := r*s+r*t+r*u+s*t+s*u+t*u
  let y : ℤ := r*s*t+r*s*u+r*t*u+s*t*u
  let z : ℤ := r*s*t*u
  have hqx : (q : ℤ) = 2*x-2*p+1 := by dsimp [x]; nlinarith only [hφ,hσ]
  have hE : y ≤ (2*(p:ℤ)+1)*x := by
    have hh := congrArg (fun a : ℤ => p*a) hqx
    have hsq := sq_nonneg ((p : ℤ)-1)
    have hrz : (1 : ℤ) ≤ r := by exact_mod_cast hrr
    have hsz : (1 : ℤ) ≤ s := by exact_mod_cast hsr
    have htz : (1 : ℤ) ≤ t := by exact_mod_cast htr
    have huz : (1 : ℤ) ≤ u := by exact_mod_cast hur
    dsimp [x,y] at *
    nlinarith only [hφ,hqx,hh,hsq,hrz,hsz,htz,huz,hp5]
  have xpos : 0 < x := by dsimp [x]; positivity
  have ypos : 0 ≤ y := by dsimp [y]; positivity
  exact inconsistent_bounds p q x y z hp5 hq2 xpos ypos hqx hE
    (by dsimp [z]; omega)
    (comp_pair_square_bound r s t u (by positivity) (by positivity) (by positivity) (by positivity))
    (newton_four r s t u)

end A056777MixedFour

#print axioms A056777MixedFour.no_mixed_four_gap_twelve
