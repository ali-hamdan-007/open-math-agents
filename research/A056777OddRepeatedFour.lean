import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777OddRepeatedFour

private theorem totient_repeated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    (p^2*q).totient = p*(p-1)*(q-1) := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 2
  have hφ : (p^2).totient = p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  rw [Nat.totient_mul hc,hφ,Nat.totient_prime hq]

private theorem sigma_repeated {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    σ 1 (p^2*q) = (p^2+p+1)*(q+1) := by
  have hc := ((Nat.coprime_primes hp hq).mpr hne).pow_left 2
  have hσp : σ 1 (p^2) = 1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hσq : σ 1 q = q+1 := by simpa using sigma_one_apply_prime_pow (i := 1) hq
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hσp,hσq]
  ring

private theorem totient_repeated_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    (r^2*s*t).totient = r*(r-1)*(s-1)*(t-1) := by
  have hc := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  rw [Nat.totient_mul hc,totient_repeated hr hs hrs,Nat.totient_prime ht]

private theorem sigma_repeated_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r^2*s*t) = (r^2+r+1)*(s+1)*(t+1) := by
  have hc := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hσt : σ 1 t = t+1 := by simpa using sigma_one_apply_prime_pow (i := 1) ht
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,sigma_repeated hr hs hrs,hσt]

private theorem odd_square_mod_eight {p : ℕ} (hp : Odd p) : p^2 % 8 = 1 := by
  have hp2 := Nat.odd_iff.mp hp
  have hres : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rw [Nat.pow_mod]
  rcases hres with h | h | h | h <;> rw [h]

private theorem shifted_mod_eight {a b f g : ℕ}
    (hgap : a+12=b ∨ b+12=a) (h : f+b=g+a) : f%8=(g+4)%8 := by omega

private theorem product_gap_moduli {a b : ℕ} (hgap : a+12=b ∨ b+12=a) :
    a%4=b%4 ∧ b%8=(a+4)%8 := by omega

private theorem residues {p q r s t : ℕ}
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : p*(p-1)*(q-1)+r^2*s*t = r*(r-1)*(s-1)*(t-1)+p^2*q)
    (hσ : (p^2+p+1)*(q+1)+r^2*s*t = (r^2+r+1)*(s+1)*(t+1)+p^2*q) :
    p % 4 = 3 ∧ q % 8 = 3 ∧ (s*t)%8 = 7 ∧ (s+t)%8 = 0 := by
  have hφmod := shifted_mod_eight hgap hφ
  have hσmod := shifted_mod_eight hgap hσ
  have ⟨hgap4,hgap8⟩ := product_gap_moduli hgap
  clear hφ hσ hgap
  have hp2 := Nat.odd_iff.mp hop
  have hq2 := Nat.odd_iff.mp hoq
  have hr2 := Nat.odd_iff.mp hor
  have hs2 := Nat.odd_iff.mp hos
  have ht2 := Nat.odd_iff.mp hot
  have hrφ : 2 ∣ r-1 := by omega
  have hsφ : 2 ∣ s-1 := by omega
  have htφ : 2 ∣ t-1 := by omega
  have hφ8 : 8 ∣ r*(r-1)*(s-1)*(t-1) :=
    mul_dvd_mul (mul_dvd_mul (dvd_mul_of_dvd_right hrφ _) hsφ) htφ
  have hdiv : ¬ 8 ∣ p*(p-1)*(q-1) := by omega
  have hp4 : p % 4 = 3 := by
    by_contra h
    have hpφ : 4 ∣ p-1 := by omega
    have hqφ : 2 ∣ q-1 := by omega
    exact hdiv (mul_dvd_mul (dvd_mul_of_dvd_right hpφ _) hqφ)
  have hq4 : q % 4 = 3 := by
    by_contra h
    have hpφ : 2 ∣ p-1 := by omega
    have hqφ : 4 ∣ q-1 := by omega
    exact hdiv (mul_dvd_mul (dvd_mul_of_dvd_right hpφ _) hqφ)
  have hp8 := odd_square_mod_eight hop
  have hr8 := odd_square_mod_eight hor
  have hp4' : p^2 % 4 = 1 := by omega
  have hr4' : r^2 % 4 = 1 := by omega
  have hn4 : (p^2*q)%4 = 3 := by rw [Nat.mul_mod,hp4',hq4]
  have hm4 : (r^2*s*t)%4 = (s*t)%4 := by
    rw [mul_assoc, Nat.mul_mod (r^2), hr4', one_mul, Nat.mod_mod]
  have hst4 : (s*t)%4 = 3 := by omega
  have hh : 4 ∣ s+1 ∨ 4 ∣ t+1 := by
    by_contra! h
    have hss : s%4=1 := by omega
    have htt : t%4=1 := by omega
    rw [Nat.mul_mod,hss,htt] at hst4
    contradiction
  have hsσ : 2 ∣ s+1 := by omega
  have htσ : 2 ∣ t+1 := by omega
  have hσ8 : 8 ∣ (r^2+r+1)*(s+1)*(t+1) := by
    rcases hh with h | h
    · exact mul_dvd_mul (dvd_mul_of_dvd_right h _) htσ
    · exact mul_dvd_mul (dvd_mul_of_dvd_right hsσ _) h
  have hq8 : q%8=3 := by
    by_contra h
    have h : 8 ∣ q+1 := by omega
    have h' := dvd_mul_of_dvd_right h (p^2+p+1)
    omega
  have hn8 : (p^2*q)%8=3 := by rw [Nat.mul_mod,hp8,hq8]
  have hm8 : (r^2*s*t)%8=(s*t)%8 := by
    rw [mul_assoc,Nat.mul_mod (r^2),hr8,one_mul,Nat.mod_mod]
  have hst8 : (s*t)%8=7 := by omega
  have hsum8 : (s+t)%8=0 := by
    rw [Nat.mul_mod] at hst8
    rw [Nat.add_mod]
    have hs8 : s%8=1 ∨ s%8=3 ∨ s%8=5 ∨ s%8=7 := by omega
    have ht8 : t%8=1 ∨ t%8=3 ∨ t%8=5 ∨ t%8=7 := by omega
    rcases hs8 with hs | hs | hs | hs <;> rcases ht8 with ht | ht | ht | ht <;>
      simp only [hs,ht] at hst8 ⊢ <;>
      first | decide | (norm_num at hst8)
  exact ⟨hp4,hq8,hst8,hsum8⟩

private theorem repeated_base_separation (p q r A B D : ℤ)
    (hp : 3 ≤ p) (hr : 3 ≤ r) (hq : 2 ≤ q) (hA : 0 ≤ A)
    (hδ : D = 12 ∨ D = -12)
    (hK : q-B-(2*r+1)*A-2*r^2+2*p=0)
    (hF : p*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^2*q-D=0)
    (hpar : p%2=1) (hrpar : r%2=1) : p+4 ≤ r := by
  have hpr : p < r := by
    by_contra! hh
    have hdiff := mul_nonneg (show 0 ≤ p-r by omega) (show 0 ≤ p+q-r-1 by omega)
    have hrK := congrArg (fun x : ℤ => r*x) hK
    have hrA := mul_nonneg (show 0 ≤ r*(r+2) by positivity) hA
    have hr₂ : 9 ≤ r^2 := by
      have hh := mul_le_mul hr hr (by decide : (0:ℤ) ≤ 3) (by omega : 0 ≤ r)
      nlinarith only [hh]
    have hpos := mul_pos (show 0 < r by omega) (show 0 < 2*r^2-2 by omega)
    nlinarith only [hF,hrK,hdiff,hrA,hpos]
  by_contra! hh
  have hre : r=p+2 := by omega
  have hL : r*(p*r+2*p-r^2+r)*A =
      D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2 := by
    linear_combination (-p*r)*hK+(p+r)*hF+hG
  rw [hre] at hL
  have hl := mul_nonneg (mul_nonneg (show 0 ≤ p+2 by omega)
    (show 0 ≤ p-2 by omega)) hA
  have hp0 : 0 ≤ p := by omega
  have hp2 : 0 ≤ p^2 := sq_nonneg p
  have hp3 : 0 ≤ p^3 := by positivity
  have hp4 : 0 ≤ p^4 := by positivity
  have hD : D ≤ 12 := by omega
  nlinarith only [hL,hl,hp,hp0,hp2,hp3,hp4,hD]

private theorem p_three_impossible {q r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hr3 : r ≠ 3) (hq2 : 2 ≤ q)
    (hgap : 3^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = 3^2*q)
    (hφ : 3*(3-1)*(q-1)+r^2*s*t = r*(r-1)*(s-1)*(t-1)+3^2*q) : False := by
  have hdiv : 3 ∣ r^2*s*t := by norm_num at hgap; omega
  simp only [Nat.prime_three.dvd_mul] at hdiv
  have hex {u : ℕ} (hu : u.Prime) (h : 3 ∣ u) : u = 3 := by
    rcases (Nat.dvd_prime hu).mp h with h | h
    · omega
    · exact h.symm
  have obstruction (v : ℕ) (hv : v.Prime)
      (hg : 3^2*q+12 = 3*(r^2*v) ∨ 3*(r^2*v)+12 = 3^2*q)
      (h : 3*(3-1)*(q-1)+3*(r^2*v) = 2*(r*(r-1)*(v-1))+3^2*q) : False := by
    norm_num at h hg
    have hmax : r^2*v ≤ r*(r-1)*(v-1)+5 := by omega
    have hr₂ := hr.two_le
    have hv₂ := hv.two_le
    have hr₁ : 1 ≤ r := hr.pos
    have hv₁ : 1 ≤ v := hv.pos
    zify [hr₁,hv₁] at hmax hr₂ hv₂
    have hprod : 6 ≤ (r:ℤ)*((r:ℤ)+v-1) :=
      mul_le_mul hr₂ (by omega : (3:ℤ) ≤ (r:ℤ)+v-1) (by decide) (by omega)
    nlinarith only [hmax,hprod]
  rcases hdiv with (hd|hd)|hd
  · exact hr3 (hex hr (Nat.prime_three.dvd_of_dvd_pow hd))
  · have he := hex hs hd
    subst s
    have he : r^2*3*t=3*(r^2*t) := by ring
    rw [he] at hgap hφ
    apply obstruction t ht hgap
    simpa only [show (3:ℕ)-1=2 by decide, mul_assoc, mul_comm, mul_left_comm] using hφ
  · have he := hex ht hd
    subst t
    have he : r^2*s*3=3*(r^2*s) := by ring
    rw [he] at hgap hφ
    apply obstruction s hs hgap
    simpa only [show (3:ℕ)-1=2 by decide, mul_assoc, mul_comm, mul_left_comm] using hφ

/-- Congruence and base separation constraints for the odd repeated/repeated
three-factor versus four-factor case of A056777. -/
theorem odd_square_prime_square_two_primes_constraints {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    p+4 ≤ r ∧ p%4=3 ∧ q%8=3 ∧ (s*t)%8=7 ∧ (s+t)%8=0 := by
  rw [totient_repeated hp hq hpq,totient_repeated_triple hr hs ht hrs hrt hst] at hφ
  rw [sigma_repeated hp hq hpq,sigma_repeated_triple hr hs ht hrs hrt hst] at hσ
  have hrules := residues hop hoq hor hos hot hgap hφ hσ
  refine ⟨?_,hrules⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; have := Nat.odd_iff.mp hop; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; have := Nat.odd_iff.mp hor; omega
  have hq2 := hq.two_le
  have hpp := Nat.odd_iff.mp hop
  have hrr := Nat.odd_iff.mp hor
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1] at hφ hσ hgap hp3 hr3 hq2 hpp hrr ⊢
  let D : ℤ := (r:ℤ)^2*s*t-(p:ℤ)^2*q
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  exact repeated_base_separation p q r (s+t) (s*t) D hp3 hr3 hq2
    (by positivity) hD (by nlinarith only [hφ,hσ]) (by nlinarith only [hφ])
    (by dsimp [D]; ring) hpp hrr

/-- The smaller repeated prime is at least seven in the odd remaining shape. -/
theorem odd_square_prime_square_two_primes_seven_le {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) : 7 ≤ p := by
  have hc := odd_square_prime_square_two_primes_constraints hp hq hr hs ht hpq hrs hrt hst
    hop hoq hor hos hot hgap hφ hσ
  have hp3 : p ≠ 3 := by
    intro he
    subst p
    rw [totient_repeated hp hq hpq,totient_repeated_triple hr hs ht hrs hrt hst] at hφ
    exact p_three_impossible hr hs ht (by have := hc.1; omega) hq.two_le hgap hφ
  have := hc.2.1
  omega

/-- The unrepeated prime on the three-factor side exceeds all primes on the four-factor side. -/
theorem odd_square_prime_square_two_primes_largest {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    r < q ∧ s < q ∧ t < q := by
  have hsep := (odd_square_prime_square_two_primes_constraints hp hq hr hs ht hpq hrs hrt hst
    hop hoq hor hos hot hgap hφ hσ).1
  rw [totient_repeated hp hq hpq,totient_repeated_triple hr hs ht hrs hrt hst] at hφ
  rw [sigma_repeated hp hq hpq,sigma_repeated_triple hr hs ht hrs hrt hst] at hσ
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  have hr2 := hr.two_le
  zify [hp1,hq1,hr1,hs1,ht1] at hφ hσ hsep hr2 ⊢
  have hK : (q:ℤ) = s*t+(2*r+1)*(s+t)+2*r^2-2*p := by
    nlinarith only [hφ,hσ]
  have hn_r := mul_nonneg (show 0 ≤ (r:ℤ) by omega) (show 0 ≤ (r:ℤ)-2 by omega)
  have hn_s := mul_nonneg (show 0 ≤ (r:ℤ) by omega) (show 0 ≤ (s:ℤ) by positivity)
  have hn_t := mul_nonneg (show 0 ≤ (r:ℤ) by omega) (show 0 ≤ (t:ℤ) by positivity)
  have hn_st : 0 ≤ (s:ℤ)*t := by positivity
  have hs0 : (0:ℤ) ≤ s := by positivity
  have ht0 : (0:ℤ) ≤ t := by positivity
  refine ⟨?_,?_,?_⟩ <;> nlinarith only [hK,hsep,hn_r,hn_s,hn_t,hn_st,hs0,ht0,hr2]

/-- The signed gap and the two equal-defect equations are equivalent to these
three equations for the prime q and the elementary symmetric functions of s,t. -/
theorem moment_criterion {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    let A : ℤ := s+t
    let B : ℤ := s*t
    ((r:ℤ)^2*B-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) ↔
    ((q:ℤ) = B+(2*r+1)*A+2*r^2-2*p ∧
      (r:ℤ)*((p:ℤ)*r+2*p-r^2+r)*A =
        D-(p:ℤ)^3+(p:ℤ)^2*r+(p:ℤ)^2-2*(p:ℤ)*r^3-(p:ℤ)*r^2+
          2*(p:ℤ)*r-(r:ℤ)^3+(r:ℤ)^2 ∧
      ((r:ℤ)^2-(p:ℤ)^2)*B = (p:ℤ)^2*((2*r+1)*A+2*r^2-2*p)+D) := by
  dsimp
  rw [totient_repeated hp hq hpq, totient_repeated_triple hr hs ht hrs hrt hst,
    sigma_repeated hp hq hpq, sigma_repeated_triple hr hs ht hrs hrt hst]
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1]
  constructor
  · rintro ⟨hG,hφ,hσ⟩
    have hK : (q:ℤ) - (s:ℤ)*t - (2*r+1)*((s:ℤ)+t)-2*(r:ℤ)^2+2*p = 0 := by
      nlinarith only [hφ,hσ]
    have hF : (p:ℤ)*((p:ℤ)+q-1)-(r:ℤ)*((s:ℤ)*t)-
        (r:ℤ)*((r:ℤ)-1)*((s:ℤ)+t-1)=0 := by
      nlinarith only [hφ]
    refine ⟨by nlinarith only [hK], ?_, ?_⟩
    · linear_combination (-(p:ℤ)*r)*hK+((p:ℤ)+r)*hF+hG
    · linear_combination (p:ℤ)^2*hK+hG
  · rintro ⟨hK,hA,hB⟩
    have hG : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D := by
      linear_combination hB-(p:ℤ)^2*hK
    have hcancel : ((p:ℤ)+r) *
        ((p:ℤ)*((p:ℤ)+q-1)-(r:ℤ)*((s:ℤ)*t)-
          (r:ℤ)*((r:ℤ)-1)*((s:ℤ)+t-1))=0 := by
      linear_combination hA+((p:ℤ)*r)*hK-hG
    have hsum : 0 < (p:ℤ) + r := by positivity
    have hF := (mul_eq_zero.mp hcancel).resolve_left hsum.ne'
    exact ⟨hG,by nlinarith only [hF],by nlinarith only [hF,hK]⟩

/-- For fixed repeated primes and a fixed signed gap, the equations fix the
unrepeated prime and the unordered pair of other primes. -/
theorem fixed_bases_unique {p r q₁ q₂ s₁ s₂ t₁ t₂ : ℕ} (D : ℤ)
    (hsep : p+4 ≤ r)
    (hp : p.Prime) (hr : r.Prime)
    (hq₁ : q₁.Prime) (hs₁ : s₁.Prime) (ht₁ : t₁.Prime)
    (hq₂ : q₂.Prime) (hs₂ : s₂.Prime) (ht₂ : t₂.Prime)
    (hpq₁ : p ≠ q₁) (hrs₁ : r ≠ s₁) (hrt₁ : r ≠ t₁) (hst₁ : s₁ ≠ t₁)
    (hpq₂ : p ≠ q₂) (hrs₂ : r ≠ s₂) (hrt₂ : r ≠ t₂) (hst₂ : s₂ ≠ t₂)
    (h₁ : (r:ℤ)^2*((s₁:ℤ)*t₁)-(p:ℤ)^2*q₁ = D ∧
      (p^2*q₁).totient+r^2*s₁*t₁ = (r^2*s₁*t₁).totient+p^2*q₁ ∧
      σ 1 (p^2*q₁)+r^2*s₁*t₁ = σ 1 (r^2*s₁*t₁)+p^2*q₁)
    (h₂ : (r:ℤ)^2*((s₂:ℤ)*t₂)-(p:ℤ)^2*q₂ = D ∧
      (p^2*q₂).totient+r^2*s₂*t₂ = (r^2*s₂*t₂).totient+p^2*q₂ ∧
      σ 1 (p^2*q₂)+r^2*s₂*t₂ = σ 1 (r^2*s₂*t₂)+p^2*q₂) :
    q₁=q₂ ∧ ((s₁=s₂ ∧ t₁=t₂) ∨ (s₁=t₂ ∧ t₁=s₂)) := by
  obtain ⟨hK₁,hA₁,hB₁⟩ := (moment_criterion D hp hq₁ hr hs₁ ht₁ hpq₁ hrs₁ hrt₁ hst₁).mp h₁
  obtain ⟨hK₂,hA₂,hB₂⟩ := (moment_criterion D hp hq₂ hr hs₂ ht₂ hpq₂ hrs₂ hrt₂ hst₂).mp h₂
  have hsep' : (p:ℤ)+4 ≤ r := by exact_mod_cast hsep
  have hr0 : 0 < (r:ℤ) := by exact_mod_cast hr.pos
  have hp0 : 0 ≤ (p:ℤ) := by positivity
  have hcoefA : (p:ℤ)*r+2*p-r^2+r < 0 := by
    have hh := mul_nonneg hr0.le (show 0 ≤ (r:ℤ)-p-4 by omega)
    nlinarith only [hh, hsep',hp0]
  have hcoefB : 0 < (r:ℤ)^2-(p:ℤ)^2 := by
    have hh := mul_pos (show 0 < (r:ℤ)-p by omega) (show 0 < (r:ℤ)+p by omega)
    nlinarith only [hh]
  have hsum : (s₁:ℤ)+t₁=(s₂:ℤ)+t₂ :=
    mul_left_cancel₀ (mul_ne_zero hr0.ne' hcoefA.ne) (hA₁.trans hA₂.symm)
  rw [hsum] at hB₁ hK₁
  have hprod : (s₁:ℤ)*t₁=(s₂:ℤ)*t₂ :=
    mul_left_cancel₀ hcoefB.ne' (hB₁.trans hB₂.symm)
  rw [hprod] at hK₁
  refine ⟨by exact_mod_cast hK₁.trans hK₂.symm,?_⟩
  have heval : ((s₁:ℤ)-s₂)*((s₁:ℤ)-t₂)=0 := by
    linear_combination (s₁:ℤ)*hsum-hprod
  rcases mul_eq_zero.mp heval with h | h
  · left
    constructor <;> omega
  · right
    constructor <;> omega

/-- The repeated prime on the four-factor side divides an explicit integer
depending only on the other repeated prime and the signed gap. -/
theorem prime_divisor_sieve {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    (r:ℤ) ∣ (p:ℤ)^2*((p:ℤ)-1)-D := by
  have hA := ((moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h).2.1
  refine ⟨(p:ℤ)^2-2*(p:ℤ)*r^2-(p:ℤ)*r+2*p-(r:ℤ)^2+r-
    ((p:ℤ)*r+2*p-r^2+r)*((s:ℤ)+t),?_⟩
  linear_combination hA

/-- The same prime divisor criterion expressed through the distance between the repeated primes. -/
theorem repeated_prime_distance_sieve {p r : ℕ} (D : ℤ)
    (h : (r:ℤ) ∣ (p:ℤ)^2*((p:ℤ)-1)-D) :
    (r:ℤ) ∣ ((r:ℤ)-p)^2*((r:ℤ)-p+1)+D := by
  obtain ⟨k,hk⟩ := h
  refine ⟨(r:ℤ)^2-3*(r:ℤ)*p+r+3*(p:ℤ)^2-2*p-k,?_⟩
  linear_combination -hk

/-- The first moment equation rewritten using the small quotient
of the integer in the prime-divisor test. -/
theorem compact_sum_criterion {p q r s t : ℕ} (D k : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hk : (p:ℤ)^2*((p:ℤ)-1)-D = (r:ℤ)*k)
    (h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    ((r:ℤ)^2-((p:ℤ)+1)*r-2*p)*((s:ℤ)+t-(2*p+1)) =
      (2*(p:ℤ)^2+4*p)*r+3*(p:ℤ)^2+k := by
  have hA := ((moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h).2.1
  have hr0 : (r:ℤ) ≠ 0 := by exact_mod_cast hr.ne_zero
  apply mul_left_cancel₀ hr0
  linear_combination -hA+hk

/-- An exact discriminant test for the existence of an ordered pair of natural
numbers with specified sum and product. -/
theorem ordered_moments_iff_discriminant (A B : ℕ) :
    (∃ s t : ℕ, s < t ∧ s+t=A ∧ s*t=B) ↔
    ∃ d : ℕ, 0 < d ∧ d ≤ A ∧ (A-d)%2=0 ∧ d^2+4*B=A^2 := by
  constructor
  · rintro ⟨s,t,hst,hs,hp⟩
    let d := t-s
    have hd : d+s=t := by dsimp [d]; omega
    refine ⟨d,by dsimp [d]; omega,by omega,by omega,?_⟩
    rw [← hs,← hp,← hd]
    ring
  · rintro ⟨d,hd,hdA,he,hsq⟩
    let s := (A-d)/2
    let t := (A+d)/2
    have hs : A=2*s+d := by dsimp [s]; omega
    have ht : t=s+d := by dsimp [s,t]; omega
    refine ⟨s,t,by omega,by omega,?_⟩
    rw [hs,ht] at hsq ⊢
    nlinarith only [hsq]

private theorem quadratic_bound_of_compact_sum (p r A D k : ℤ)
    (hp : 7 ≤ p) (hr : p+4 ≤ r) (hD : D=12 ∨ D=-12)
    (hk : p^2*(p-1)-D=r*k)
    (hA : (r^2-(p+1)*r-2*p)*(A-(2*p+1))=(2*p^2+4*p)*r+3*p^2+k) :
    r ≤ 3*p^2 := by
  have hp0 : 0 < p := by omega
  have hr0 : 0 < r := by omega
  have hp2 : 49 ≤ p^2 := by
    have hh := mul_le_mul hp hp (by decide : (0:ℤ) ≤ 7) hp0.le
    nlinarith only [hh]
  have hk0 : 0 ≤ k := by
    by_contra! h
    have hn := mul_neg_of_pos_of_neg hr0 h
    have hp3 := mul_nonneg (sq_nonneg p) (show 0 ≤ p-2 by omega)
    have hD' : D ≤ 12 := by omega
    nlinarith only [hn,hp3,hp2,hk,hD']
  have hk' : k ≤ p^2 := by
    by_contra! h
    have hh := mul_pos (show 0 < k-p^2 by omega) hr0
    have hh' := mul_nonneg (sq_nonneg p) (show 0 ≤ r-p by omega)
    have hD' : -12 ≤ D := by omega
    nlinarith only [hh,hh',hk,hD',hp2]
  have h∆ : 0 < r^2-(p+1)*r-2*p := by
    have hh := mul_nonneg hr0.le (show 0 ≤ r-p-4 by omega)
    nlinarith only [hh,hr,hp0]
  have hpos : 0 < A-(2*p+1) := by
    by_contra! h
    have hh := mul_nonpos_of_nonneg_of_nonpos h∆.le h
    have hh' := mul_nonneg hr0.le (show 0 ≤ 2*p^2+4*p by positivity)
    nlinarith only [hh,hh',hA,hp2,hk0]
  have hquad : r^2-(p+1)*r-2*p ≤ (2*p^2+4*p)*r+4*p^2 := by
    have hh := mul_nonneg h∆.le (show 0 ≤ A-(2*p+1)-1 by omega)
    nlinarith only [hh,hA,hk']
  by_contra! h
  have hp' := mul_nonneg (show 0 ≤ p-7 by omega) (show 0 ≤ p+2 by omega)
  have hh : 2 ≤ r-(2*p^2+5*p+1) := by nlinarith only [h,hp']
  have hlow := mul_le_mul_of_nonneg_right hh hr0.le
  have hq := mul_nonneg hp0.le (show 0 ≤ p-1 by omega)
  nlinarith only [hquad,hlow,h,hq]

/-- In the odd remaining class, the larger repeated prime is quadratically bounded
by the smaller one. Combined with the prime-divisor condition, this is a finite
sieve for every fixed p and signed orientation. -/
theorem repeated_prime_quadratic_bound {p q r s t : ℕ} (D : ℤ)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hp7 : 7 ≤ p) (hsep : p+4 ≤ r) (hD : D=12 ∨ D=-12)
    (h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q = D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) :
    r ≤ 3*p^2 := by
  obtain ⟨k,hk⟩ := prime_divisor_sieve D hp hq hr hs ht hpq hrs hrt hst h
  have hh := compact_sum_criterion D k hp hq hr hs ht hpq hrs hrt hst hk h
  have hbound := quadratic_bound_of_compact_sum p r ((s:ℤ)+t) D k
    (by exact_mod_cast hp7) (by exact_mod_cast hsep) hD hk hh
  exact_mod_cast hbound

end A056777OddRepeatedFour

#print axioms A056777OddRepeatedFour.odd_square_prime_square_two_primes_constraints

#print axioms A056777OddRepeatedFour.odd_square_prime_square_two_primes_seven_le

#print axioms A056777OddRepeatedFour.odd_square_prime_square_two_primes_largest

#print axioms A056777OddRepeatedFour.moment_criterion
#print axioms A056777OddRepeatedFour.fixed_bases_unique
#print axioms A056777OddRepeatedFour.prime_divisor_sieve
#print axioms A056777OddRepeatedFour.repeated_prime_distance_sieve

#print axioms A056777OddRepeatedFour.compact_sum_criterion
#print axioms A056777OddRepeatedFour.ordered_moments_iff_discriminant
#print axioms A056777OddRepeatedFour.repeated_prime_quadratic_bound
