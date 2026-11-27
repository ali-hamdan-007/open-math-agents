import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open Nat

namespace A056777CubePrimeFourFour

private theorem totient_defect_cube_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p^3*q).totient + p^2*(p+q-1) = p^3*q := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 3
  rw [Nat.totient_mul hc, show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2,
    Nat.totient_prime hq]
  have hp₁ := hp.pos
  have hq₁ := hq.pos
  have hpq₁ : 1 ≤ p+q := by omega
  zify [hp₁,hq₁,hpq₁]
  ring

private theorem no_ordered_cube_prime_pair {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hpr : p < r)
    (hgap : p^3*q+12 = r^3*s ∨ r^3*s+12 = p^3*q)
    (hφ : (p^3*q).totient+r^3*s = (r^3*s).totient+p^3*q) : False := by
  let F := p^2*(p+q-1)
  have hF : F=r^2*(r+s-1) := by
    dsimp [F]
    have h₁ := totient_defect_cube_mul_prime hp hq hpq
    have h₂ := totient_defect_cube_mul_prime hr hs hrs
    omega
  have hpD : p^2 ∣ F := dvd_mul_right _ _
  have hrD : r^2 ∣ F := hF ▸ dvd_mul_right _ _
  have hc := (((Nat.coprime_primes hp hr).mpr hpr.ne).pow_left 2).pow_right 2
  have hFD : p^2*r^2 ∣ F := hc.mul_dvd_of_dvd_of_dvd hpD hrD
  have hFpos : 0 < F := by
    have hpq' : 0 < p+q-1 := by have := hp.two_le; have := hq.two_le; omega
    dsimp [F]
    exact mul_pos (pow_pos hp.pos _) hpq'
  have hFlow := Nat.le_of_dvd hFpos hFD
  have hp₁ := hp.pos
  have hr₁ := hr.pos
  have hq₁ := hq.pos
  have hs₁ := hs.pos
  have hpq₁ : 1 ≤ p+q := by omega
  have hrs₁ : 1 ≤ r+s := by omega
  have hF₁ : F=p^2*(p+q-1) := rfl
  zify [hp₁,hr₁,hq₁,hs₁,hpq₁,hrs₁] at hF hF₁ hgap hFlow hpr
  let D : ℤ := (r:ℤ)^3*s-(p:ℤ)^3*q
  let K : ℤ := (r:ℤ)^3+(r:ℤ)^2*p+(r:ℤ)*p^2+(p:ℤ)^3-
    ((r:ℤ)^2+(r:ℤ)*p+(p:ℤ)^2)
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  have he : D=((r:ℤ)-p)*((F:ℤ)-K) := by
    dsimp only [D,K]
    linear_combination -(r:ℤ)*hF+(p:ℤ)*hF₁
  have hd : (r:ℤ)-p ∣ (12:ℤ) := by
    rcases hD with h | h
    · exact ⟨(F:ℤ)-K,h.symm.trans he⟩
    · refine ⟨-((F:ℤ)-K),?_⟩
      linear_combination h-he
  have hdiff_le : (r:ℤ)-p ≤ 12 := Int.le_of_dvd (by decide) hd
  have hKle : K ≤ 4*(r:ℤ)^3 := by
    have hp0 : (0:ℤ) ≤ p := by positivity
    have hr0 : (0:ℤ) ≤ r := by positivity
    have hpr' : (p:ℤ) ≤ r := hpr.le
    have hq2 := mul_le_mul hpr' hpr' hp0 hr0
    have h₁ := mul_le_mul_of_nonneg_left hpr' (sq_nonneg (r:ℤ))
    have h₂ := mul_le_mul_of_nonneg_left hq2 hr0
    have h₃ := mul_le_mul hq2 hpr' hp0 (mul_nonneg hr0 hr0)
    dsimp only [K]
    nlinarith only [h₁,h₂,h₃,sq_nonneg (r:ℤ),sq_nonneg (p:ℤ),mul_nonneg hr0 hp0]
  have hFup : (F:ℤ) ≤ 4*(r:ℤ)^3+12 := by
    have hsmall : (F:ℤ)-K ≤ 12 := by
      by_contra! h
      have hh := mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ (r:ℤ)-p by omega)
        (show (0:ℤ) ≤ (F:ℤ)-K by omega)
      nlinarith only [hh,he,show D ≤ 12 by omega,h]
    omega
  have hp10 : p ≤ 10 := by
    by_contra! h
    have h11 : (11:ℤ) ≤ p := by exact_mod_cast h
    have h5 : 5*(r:ℤ) ≤ (p:ℤ)^2 := by
      have hh := mul_nonneg (show 0 ≤ (p:ℤ)-11 by omega) (show 0 ≤ (p:ℤ)+6 by omega)
      nlinarith only [hh,hdiff_le]
    have hh := mul_le_mul_of_nonneg_right h5 (sq_nonneg (r:ℤ))
    have hr3 : (3:ℤ) ≤ r := by omega
    have hr9 : 9 ≤ (r:ℤ)^2 := by
      have := mul_le_mul hr3 hr3 (by decide : (0:ℤ) ≤ 3) (show 0 ≤ (r:ℤ) by omega)
      nlinarith only [this]
    have hr27 : 27 ≤ (r:ℤ)^3 := by
      have := mul_le_mul hr9 hr3 (by decide : (0:ℤ) ≤ 3) (sq_nonneg (r:ℤ))
      nlinarith only [this]
    nlinarith only [hFlow,hFup,hh,hr27]
  have hr22 : r ≤ 22 := by omega
  have pchoices : p=2 ∨ p=3 ∨ p=5 ∨ p=7 := by
    interval_cases p <;> first | decide | (exfalso; exact (by decide : ¬Nat.Prime _) hp)
  have rchoices : r=2 ∨ r=3 ∨ r=5 ∨ r=7 ∨ r=11 ∨ r=13 ∨ r=17 ∨ r=19 := by
    interval_cases r <;> first | decide | (exfalso; exact (by decide : ¬Nat.Prime _) hr)
  rcases pchoices with rp|rp|rp|rp <;> rcases rchoices with rr|rr|rr|rr|rr|rr|rr|rr <;>
    subst p <;> subst r <;> norm_num [K] at he hFD hpr <;> omega

/-- Both orientations of a twelve-step between cube-times-prime four-factor
endpoints are impossible. The totient equation by itself suffices. -/
theorem no_cube_prime_cube_prime_gap_twelve {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hgap : p^3*q+12 = r^3*s ∨ r^3*s+12 = p^3*q)
    (hφ : (p^3*q).totient+r^3*s = (r^3*s).totient+p^3*q) : False := by
  rcases lt_trichotomy p r with h | h | h
  · exact no_ordered_cube_prime_pair hp hq hr hs hpq hrs h hgap hφ
  · subst r
    have h₁ := totient_defect_cube_mul_prime hp hq hpq
    have h₂ := totient_defect_cube_mul_prime hp hs hrs
    have he : p^2*(p+q-1) = p^2*(p+s-1) := by omega
    have he' := Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) he
    have hqs : q=s := by have := hp.pos; omega
    subst s
    omega
  · refine no_ordered_cube_prime_pair hr hs hp hq hrs hpq h ?_ hφ.symm
    exact hgap.symm

end A056777CubePrimeFourFour

#print axioms A056777CubePrimeFourFour.no_cube_prime_cube_prime_gap_twelve
