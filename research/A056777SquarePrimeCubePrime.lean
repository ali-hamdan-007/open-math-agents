import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777SquarePrimeCubePrime

private theorem no_defect_collision {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hF : p * (p + q - 1) = r^2 * (r + s - 1))
    (hK : q + 2*p = (r+1)*s + 2*r^2 + r) : False := by
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  by_cases hpr : p = r
  · subst r
    have hF' : p + q - 1 = p*(p+s-1) := by
      apply Nat.eq_of_mul_eq_mul_left hp1
      calc
        p*(p+q-1) = p^2*(p+s-1) := hF
        _ = p*(p*(p+s-1)) := by ring
    have hpq : 1 ≤ p + q := by omega
    have hps : 1 ≤ p + s := by omega
    zify [hpq, hps] at hF' hK hp1 hs1
    nlinarith [sq_nonneg (p : ℤ)]
  have hcop := (Nat.coprime_primes hp hr).mpr hpr
  have hdiv : p ∣ r+s-1 :=
    (hcop.pow_right 2).dvd_of_dvd_mul_left ⟨p+q-1, hF.symm⟩
  obtain ⟨t, ht⟩ := hdiv
  have ht1 : 1 ≤ t := by
    by_contra! h
    have hz : t = 0 := by omega
    simp [hz] at ht
    omega
  have hx : p + q - 1 = r^2*t := by
    apply Nat.eq_of_mul_eq_mul_left hp1
    rw [hF, ht]
    ring
  have hpq : 1 ≤ p+q := by omega
  have hrs : 1 ≤ r+s := by omega
  have hrz : 0 < (r : ℤ) := by exact_mod_cast hr1
  have hpz : 0 < (p : ℤ) := by exact_mod_cast hp1
  have htz : 1 ≤ (t : ℤ) := by exact_mod_cast ht1
  have hz : ((r : ℤ)^2 - p*(r+1))*((t : ℤ)-1) = r*(p+1) := by
    zify [hpq, hrs] at hx ht hK
    have hmul := congrArg (fun a : ℤ => ((r : ℤ)+1)*a) ht
    nlinarith only [hx, hmul, hK]
  have hDpos : (0 : ℤ) < (r : ℤ)^2 - p*(r+1) := by
    by_contra! hn
    have hn' := mul_nonpos_of_nonpos_of_nonneg hn (show (0 : ℤ) ≤ (t : ℤ)-1 by omega)
    rw [hz] at hn'
    have hpos : (0 : ℤ) < (r : ℤ)*(p+1) := mul_pos hrz (by omega)
    omega
  have hle : p*(r+1) ≤ r^2 := by
    zify
    omega
  let D := r^2-p*(r+1)
  have hsum : D+p*(r+1) = r^2 := by dsimp [D]; omega
  have hprod : D*(t-1) = r*(p+1) := by
    dsimp [D]
    zify [hle, ht1]
    exact hz
  have hrd : ¬r ∣ D := by
    intro hd
    have hr2 : r ∣ r^2 := ⟨r, by ring⟩
    have hadd : r ∣ D+p*(r+1) := hsum ▸ hr2
    have hpm : r ∣ p*(r+1) := (Nat.dvd_add_iff_right hd).mpr hadd
    rcases hr.dvd_mul.mp hpm with hh | hh
    · exact hpr ((Nat.prime_dvd_prime_iff_eq hr hp).mp hh).symm
    · have h := (Nat.dvd_add_iff_right (dvd_refl r)).mpr hh
      exact hr.not_dvd_one h
  have hrprod : r ∣ D*(t-1) := ⟨p+1, hprod⟩
  obtain ⟨u, hu⟩ := (hr.dvd_mul.mp hrprod).resolve_left hrd
  have hdu : D*u = p+1 := by
    apply Nat.eq_of_mul_eq_mul_left hr1
    calc
      r*(D*u) = D*(r*u) := by ring
      _ = r*(p+1) := by rw [← hu, hprod]
  have hu1 : 1 ≤ u := by
    by_contra! hn
    have hu0 : u = 0 := by omega
    simp [hu0] at hdu
  have hDle : D ≤ p+1 := by
    calc D = D*1 := by simp
      _ ≤ D*u := Nat.mul_le_mul_left D hu1
      _ = p+1 := hdu
  have hpr' : p < r := by
    by_contra! hn
    have h := Nat.mul_le_mul_right (r+1) hn
    zify at h
    nlinarith only [h, hDpos, hrz]
  have hrp : r = p+1 := by
    by_contra he
    have hprt : p+2 ≤ r := by omega
    have hh := Nat.mul_le_mul_right (r+1) hprt
    zify at hh hDle
    have hcast : (D : ℤ) = (r : ℤ)^2-p*(r+1) := by
      dsimp [D]
      push_cast [Nat.cast_sub hle]
      rfl
    rw [hcast] at hDle
    zify at hprt
    nlinarith only [hh, hDle, hprt]
  have hp2 : p = 2 := by
    rcases hp.eq_two_or_odd with he | ho
    · exact he
    rcases hr.eq_two_or_odd with he | hodd
    · have := hp.two_le
      omega
    · omega
  have hr3 : r = 3 := by omega
  subst p
  subst r
  have hD1 : D = 1 := by decide
  rw [hD1, one_mul] at hprod
  have hs18 : s = 18 := by omega
  subst s
  exact (by decide : ¬Nat.Prime 18) hs

/-- No square-times-prime and cube-times-prime endpoints have equal totient and
divisor-sum defects. This excludes the two orientations of a gap of twelve. -/
theorem no_squarePrime_cubePrime {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hφ : (p^2*q).totient + r^3*s = (r^3*s).totient + p^2*q)
    (hσ : σ 1 (p^2*q) + r^3*s = σ 1 (r^3*s) + p^2*q) : False := by
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hcr := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 3
  have hσp {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hσ₂ : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hσ₃ : σ 1 (r^3) = 1+r+r^2+r^3 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hφ₂ : (p^2).totient = p*(p-1) := by
    simpa using Nat.totient_prime_pow_succ hp 1
  have hφ₃ : (r^3).totient = r^2*(r-1) := Nat.totient_prime_pow_succ hr 2
  rw [Nat.totient_mul hcp, Nat.totient_mul hcr, hφ₂, hφ₃,
    Nat.totient_prime hq, Nat.totient_prime hs] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp, isMultiplicative_sigma.map_mul_of_coprime hcr,
    hσ₂, hσ₃, hσp hq, hσp hs] at hσ
  apply no_defect_collision hp hq hr hs
  · have hpq1 : 1 ≤ p+q := by have := hp.pos; omega
    have hrs1 : 1 ≤ r+s := by have := hr.pos; omega
    have hp1 := hp.pos
    have hq1 := hq.pos
    have hr1 := hr.pos
    have hs1 := hs.pos
    zify [hpq1, hrs1, hp1, hq1, hr1, hs1] at hφ ⊢
    nlinarith only [hφ]
  · have hp1 := hp.pos
    have hq1 := hq.pos
    have hr1 := hr.pos
    have hs1 := hs.pos
    zify [hp1, hq1, hr1, hs1] at hφ hσ ⊢
    nlinarith only [hφ, hσ]

end A056777SquarePrimeCubePrime

#print axioms A056777SquarePrimeCubePrime.no_squarePrime_cubePrime
