import A056777CubeFour
import A056777EvenFourFourCore
import A056777Closure
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777EvenSquarefreeThreeFive

private theorem cube_excess {p : ℕ} (hp : p.Prime) :
    σ 1 (p^3)+(p^3).totient=2*p^3+p+1 := by
  have hsigma : σ 1 (p^3)=1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [hsigma,show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
  have hp1 := hp.pos
  zify [hp1]
  ring

private theorem mul_prime_excess_lower {a p k : ℕ} (ha : a≠0) (hp : p.Prime)
    (hc : a.Coprime p) (h : 2*a+k≤σ 1 a+a.totient) :
    2*(a*p)+p*k≤σ 1 (a*p)+(a*p).totient := by
  have hsigma : a≤σ 1 a := by
    rw [sigma_one_apply]
    exact Finset.single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨by simp,ha⟩)
  have hφ := Nat.totient_le a
  have hsigmap : σ 1 p=p+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hp
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hsigmap,Nat.totient_mul hc,Nat.totient_prime hp]
  have hp1 := hp.pos
  have hh := Nat.mul_le_mul_left p h
  zify [hp1] at hh hsigma hφ ⊢
  nlinarith only [hh,hsigma,hφ]

private theorem odd_core_excess_not_six_or_negative {m : ℕ} (ho : Odd m)
    (hm : m.primeFactorsList.length=4) :
    ¬(σ 1 m+m.totient=2*m+6 ∨ σ 1 m+m.totient+2=2*m) := by
  intro he
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨p,q,hp,hq,hpq,rfl⟩ |
    ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩ | ⟨p,q,r,s,hp,hq,hr,hs,hpq,hpr,hps,hqr,hqs,hrs,rfl⟩
  · have hm0 : m≠0 := by rintro rfl; simp at hm
    have hlarge : 2<m := by
      by_contra! h
      interval_cases m <;> simp at hm
    have hsigma := Nat.odd_iff.mp ((A056777Parity.odd_sigma_iff_square_or_twice_square hm0).mpr
      (Or.inl ⟨k,hk⟩))
    have hφ := Nat.even_iff.mp (Nat.totient_even hlarge)
    omega
  · have hqodd := (Nat.odd_mul.mp ho).2
    have hq3 : 3≤q := by have := hq.two_le; have := Nat.odd_iff.mp hqodd; omega
    have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
    have hk : 2*p^3+(p+1)≤σ 1 (p^3)+(p^3).totient := by have hh := cube_excess hp; omega
    have h := mul_prime_excess_lower (pow_ne_zero _ hp.ne_zero) hq hc hk
    have hp2 := hp.two_le
    have hmul : 9≤q*(p+1) := Nat.mul_le_mul hq3 (by omega : 3≤p+1)
    omega
  · have hc := (((Nat.coprime_primes hp hr).mpr hpr).pow_left 2).mul_left
      ((Nat.coprime_primes hq hr).mpr hqr)
    have hb := (A056777EvenFourFour.square_prime_formulas hp hq hpq).2
    have hk : 2*(p^2*q)+(q+2*p+1)≤σ 1 (p^2*q)+(p^2*q).totient := by omega
    have hh := mul_prime_excess_lower (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hq.ne_zero) hr hc hk
    have hp2 := hp.two_le
    have hq2 := hq.two_le
    have hmul : 14≤r*(q+2*p+1) := Nat.mul_le_mul hr.two_le (by omega : 7≤q+2*p+1)
    omega
  · have hc₁ := (Nat.coprime_primes hp hq).mpr hpq
    have hc₂ := ((Nat.coprime_primes hp hr).mpr hpr).mul_left ((Nat.coprime_primes hq hr).mpr hqr)
    have hc₃ := (((Nat.coprime_primes hp hs).mpr hps).mul_left
      ((Nat.coprime_primes hq hs).mpr hqs)).mul_left ((Nat.coprime_primes hr hs).mpr hrs)
    have hfree : Squarefree (p*q*r*s) := Nat.squarefree_mul_iff.mpr ⟨hc₃,Nat.squarefree_mul_iff.mpr
      ⟨hc₂,Nat.squarefree_mul_iff.mpr ⟨hc₁,hp.squarefree,hq.squarefree⟩,hr.squarefree⟩,hs.squarefree⟩
    have h := A056777Closure.low_excess_of_odd_squarefree (p*q*r*s) ho hfree
    omega

private theorem length_mul_two {n : ℕ} (hn : n≠0) :
    (2*n).primeFactorsList.length=1+n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2:ℕ)≠0) hn).length_eq
  rwa [Nat.primeFactorsList_two,List.length_append,List.length_singleton] at hh

/-- An even squarefree three-factor endpoint has no five-factor partner in either orientation. -/
theorem no_even_squarefree_three_five_pair {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (he : Even n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  have hnd : ¬4∣n := Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two
  have hme : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hme
  have hna : n=2*a := by omega
  have hmb : m=2*b := by omega
  have hoa : Odd a := Nat.odd_iff.mpr (by omega)
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have ha0 : a≠0 := by have := Nat.odd_iff.mp hoa; omega
  have hb0 : b≠0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length=2 := by rw [hna,length_mul_two ha0] at hn; omega
  have hbl : b.primeFactorsList.length=4 := by rw [hmb,length_mul_two hb0] at hm; omega
  have hsf' : Squarefree (2*a) := hna ▸ hs
  have hsa := hsf'.squarefree_of_dvd (dvd_mul_left a 2)
  have ha1 : 1<a := by
    by_contra! h
    interval_cases a <;> simp at hal
  have hap : ¬a.Prime := by intro h; simp [Nat.primeFactorsList_prime h] at hal
  have hsem : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a=p*q := by
    by_contra h
    have hh := A056777Closure.factor_count_of_nonsemiprime ha1 hap h
    omega
  obtain ⟨p,q,hp,hq,hapq⟩ := hsem
  have hpq : p≠q := by
    rintro rfl
    exact Nat.squarefree_iff_prime_squarefree.mp hsa p hp ⟨1,by simp [hapq]⟩
  have hsmall := (A056777Closure.excess_two_iff a).mpr ⟨p,q,hp,hq,hpq,hapq⟩
  have hca := hoa.coprime_two_left
  have hcb := hob.coprime_two_left
  rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hφ
  norm_num at hφ
  rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
    isMultiplicative_sigma.map_mul_of_coprime hcb,show σ 1 2=3 by decide] at hσ
  exact odd_core_excess_not_six_or_negative hob hbl (by omega)

end A056777EvenSquarefreeThreeFive

#print axioms A056777EvenSquarefreeThreeFive.no_even_squarefree_three_five_pair
