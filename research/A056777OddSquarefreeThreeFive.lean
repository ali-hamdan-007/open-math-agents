import A056777OddFour
import Mathlib.Tactic.IntervalCases

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777OddSquarefreeThreeFive

private theorem odd_prime_factor {n p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hd : p∣n) : Odd p := by
  rcases hp.eq_two_or_odd' with rfl|h
  · have hm := Nat.odd_iff.mp hn
    omega
  · exact h

private theorem odd_square_mod_four {p : ℕ} (h : Odd p) : p^2%4=1 := by
  have hov := Nat.odd_iff.mp h
  have hres : p%4=1 ∨ p%4=3 := by omega
  rw [Nat.pow_mod]
  rcases hres with h|h <;> rw [h]

private theorem sigma_fifth_not_four_mod_eight {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hφ : (p^5).totient%8=4) : σ 1 (p^5)%8 ≠ 4 := by
  have hd : 4∣(p^5).totient := by omega
  have hφp : (p^5).totient=p^4*(p-1) := Nat.totient_prime_pow_succ hp 4
  rw [hφp] at hd
  have hc := (ho.coprime_two_left.pow_left 2).pow_right 4
  have hp4 : 4∣p-1 := hc.dvd_of_dvd_mul_left hd
  have hp1 : 1≤p := hp.pos
  have hpplus : (p+1)%4=2 := by omega
  have hpp := odd_square_mod_four ho
  have hpiv : p^4%4=1 := by
    rw [show p^4=(p^2)^2 by ring,Nat.pow_mod, hpp]
  have hgeom : (p^4+p^2+1)%4=3 := by omega
  have hs : σ 1 (p^5)=(p+1)*(p^4+p^2+1) := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
    ring
  have hs4 : σ 1 (p^5)%4=2 := by rw [hs,Nat.mul_mod,hpplus,hgeom]
  omega

private theorem odd_bases_mod_four {p q a b : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p≠q)
    (hop : Odd p) (hoq : Odd q) (ha : 0<a) (hb : 0<b)
    (hnd : ¬8∣(p^a*q^b).totient) : p%4=3 ∧ q%4=3 := by
  have hoc := (((Nat.coprime_primes hp hq).mpr hne).pow_left a).pow_right b
  have hφ : (p^a*q^b).totient=(p^(a-1)*(p-1))*(q^(b-1)*(q-1)) := by
    rw [Nat.totient_mul hoc,Nat.totient_prime_pow hp ha,Nat.totient_prime_pow hq hb]
  have hp2 := Nat.odd_iff.mp hop
  have hq2 := Nat.odd_iff.mp hoq
  constructor
  · by_contra h
    have h4 : 4∣p-1 := by omega
    have h2 : 2∣q-1 := by omega
    exact hnd (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right h4 _) (dvd_mul_of_dvd_right h2 _))
  · by_contra h
    have h2 : 2∣p-1 := by omega
    have h4 : 4∣q-1 := by omega
    exact hnd (hφ ▸ mul_dvd_mul (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h4 _))

private theorem cube_square_sigma_eight {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p≠q) (h4 : p%4=3)
    (ho : Odd p) : 8∣σ 1 (p^3*q^2) := by
  have hc := (((Nat.coprime_primes hp hq).mpr hne).pow_left 3).pow_right 2
  have h : σ 1 (p^3)=(p+1)*(p^2+1) := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
    ring
  have hpD : 4∣p+1 := by omega
  have hpD' : 2∣p^2+1 := by have := odd_square_mod_four ho; omega
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,h]
  exact dvd_mul_of_dvd_left (mul_dvd_mul hpD hpD') _

private theorem quintic_shape {m : ℕ}
    (hm : Odd m) (hlen : m.primeFactorsList.length=5)
    (hφ : m.totient%8=4) (hσ : σ 1 m%8=4) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ p%4=3 ∧ q%8=3 ∧ m=p^4*q := by
  have hm0 : m≠0 := by have := Nat.odd_iff.mp hm; omega
  have hnd : ¬8∣m.totient := by omega
  have hcard : m.primeFactors.card≤2 := by
    by_contra! h
    exact hnd ((pow_dvd_pow 2 h).trans (A056777OddFour.two_pow_card_dvd_totient hm))
  have hpos : 0<m.primeFactors.card := by
    by_contra! h
    have he : m.primeFactors=∅ := Finset.card_eq_zero.mp (by omega)
    rcases Nat.primeFactors_eq_empty.mp he with rfl|rfl <;> simp at hlen
  have hprod := Nat.prod_factorization_pow_eq_self hm0
  rw [Finsupp.prod,Nat.support_factorization] at hprod
  rcases (show m.primeFactors.card=1 ∨ m.primeFactors.card=2 by omega) with h₁|h₂
  · obtain ⟨p,hpF⟩ := Finset.card_eq_one.mp h₁
    have hmem : p∈m.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hmem
    have hop := odd_prime_factor hm hp (Nat.mem_primeFactors.mp hmem).2.1
    rw [hpF,Finset.prod_singleton] at hprod
    rw [← hprod,hp.primeFactorsList_pow,List.length_replicate] at hlen
    rw [hlen] at hprod
    rw [←hprod] at hφ hσ
    exact (sigma_fifth_not_four_mod_eight hp hop hφ hσ).elim
  · obtain ⟨p,q,hne,hpF⟩ := Finset.card_eq_two.mp h₂
    have hpm : p∈m.primeFactors := by simp [hpF]
    have hqm : q∈m.primeFactors := by simp [hpF]
    have hp := Nat.prime_of_mem_primeFactors hpm
    have hq := Nat.prime_of_mem_primeFactors hqm
    have hop := odd_prime_factor hm hp (Nat.mem_primeFactors.mp hpm).2.1
    have hoq := odd_prime_factor hm hq (Nat.mem_primeFactors.mp hqm).2.1
    let a := m.factorization p
    let b := m.factorization q
    have ha : 0<a := hp.factorization_pos_of_dvd hm0 (Nat.mem_primeFactors.mp hpm).2.1
    have hb : 0<b := hq.factorization_pos_of_dvd hm0 (Nat.mem_primeFactors.mp hqm).2.1
    rw [hpF,Finset.prod_insert (by simpa using hne),Finset.prod_singleton] at hprod
    change p^a*q^b=m at hprod
    have hlen' := (Nat.perm_primeFactorsList_mul (pow_ne_zero a hp.ne_zero)
      (pow_ne_zero b hq.ne_zero)).length_eq
    rw [hprod,hlen,hp.primeFactorsList_pow,hq.primeFactorsList_pow,
      List.length_append,List.length_replicate,List.length_replicate] at hlen'
    have hnd' : ¬8∣(p^a*q^b).totient := by rw [hprod]; exact hnd
    obtain ⟨hp4,hq4⟩ := odd_bases_mod_four hp hq hne hop hoq ha hb hnd'
    have rcase : (a=4 ∧ b=1) ∨ (a=1 ∧ b=4) ∨ (a=3 ∧ b=2) ∨ (a=2 ∧ b=3) := by omega
    have residue_of_four_mul {u v : ℕ} (hu : u.Prime) (hv : v.Prime)
        (hneq : u≠v) (hv4 : v%4=3) (he : u^4*v=m) : v%8=3 := by
      have hc := ((Nat.coprime_primes hu hv).mpr hneq).pow_left 4
      have hsigv : σ 1 v=v+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hv
      by_contra hn
      have hvD : 8∣v+1 := by omega
      rw [←he,isMultiplicative_sigma.map_mul_of_coprime hc,hsigv] at hσ
      have hd := dvd_mul_of_dvd_right hvD (σ 1 (u^4))
      omega
    rcases rcase with ⟨ha',hb'⟩ | ⟨ha',hb'⟩ | ⟨ha',hb'⟩ | ⟨ha',hb'⟩ <;>
      rw [ha',hb'] at hprod
    · rw [pow_one] at hprod
      exact ⟨p,q,hp,hq,hne,hp4,residue_of_four_mul hp hq hne hq4 hprod,hprod.symm⟩
    · rw [pow_one,mul_comm] at hprod
      exact ⟨q,p,hq,hp,hne.symm,hq4,residue_of_four_mul hq hp hne.symm hp4 hprod,hprod.symm⟩
    · rw [←hprod] at hσ
      have hd := cube_square_sigma_eight hp hq hne hp4 hop
      omega
    · rw [mul_comm] at hprod
      rw [←hprod] at hσ
      have hd := cube_square_sigma_eight hq hp hne.symm hq4 hoq
      omega

/-- An odd squarefree three-factor endpoint can only be paired with an odd p⁴q
endpoint on the five-factor side. The two jump equalities impose the displayed
residues on the repeated prime and the other prime. -/
theorem remaining_odd_squarefree_three_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5)
    (hs : Squarefree n) (ho : Odd n)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ p%4=3 ∧ q%8=3 ∧ m=p^4*q := by
  have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
  have hncard : 3≤n.primeFactors.card := by
    rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hn]
  have hdφ : 8∣n.totient := (pow_dvd_pow 2 hncard).trans
    (A056777OddFour.two_pow_card_dvd_totient ho)
  have hfilt : (n.primeFactors.filter fun p => p≠2 ∧ Odd (n.factorization p))=n.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have ⟨hpp,hpd,hzero⟩ := Nat.mem_primeFactors.mp hp
    have ho' := odd_prime_factor ho hpp hpd
    have hp2 : p≠2 := by rintro rfl; exact (by decide : ¬Odd 2) ho'
    have hpos := hpp.factorization_pos_of_dvd hzero hpd
    have hle := hs.natFactorization_le_one p
    have h1 : n.factorization p=1 := by omega
    exact ⟨hp2,h1 ▸ (by decide : Odd 1)⟩
  have hd := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hs.ne_zero
  rw [hfilt] at hd
  have hdσ : 8∣σ 1 n := (pow_dvd_pow 2 hncard).trans hd
  exact quintic_shape hom hm (by omega) (by omega)

end A056777OddSquarefreeThreeFive

#print axioms A056777OddSquarefreeThreeFive.remaining_odd_squarefree_three_five
