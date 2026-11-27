import A056777FourFourShapes
import A056777RepeatedTriple
import A056777EvenFourFourMixedCore

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777EvenFourFour

private theorem seven_dvd_sigma_of_four_dvd {n : ℕ}
    (h : Squarefree n ∨ A056777FourFour.RepeatedFour n) (hd : 4 ∣ n) : 7 ∣ σ 1 n := by
  rcases h with hs | ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,rfl⟩
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hd).elim
  have hp2 : p=2 := by
    by_contra hne
    have hc := (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hne)).pow_left 2).pow_right 2
    rw [mul_assoc] at hd
    have hd' : 4 ∣ q*r := hc.dvd_of_dvd_mul_left hd
    have hs : Squarefree (q*r) := Nat.squarefree_mul_iff.mpr
      ⟨(Nat.coprime_primes hq hr).mpr hqr,hq.squarefree,hr.squarefree⟩
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hd'
  subst p
  have hc := (((Nat.coprime_primes Nat.prime_two hq).mpr hpq).mul_right
    ((Nat.coprime_primes Nat.prime_two hr).mpr hpr)).pow_left 2
  rw [mul_assoc,isMultiplicative_sigma.map_mul_of_coprime hc,show σ 1 ((2:ℕ)^2)=7 by decide]
  exact dvd_mul_right _ _

private theorem length_mul_two {n : ℕ} (hn : n ≠ 0) :
    (2*n).primeFactorsList.length=1+n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2:ℕ)≠0) hn).length_eq
  rwa [Nat.primeFactorsList_two,List.length_append,List.length_singleton] at hh

private theorem core_nonsquarefree {a : ℕ}
    (ha : Odd a) (h : A056777FourFour.RepeatedFour (2*a)) : ¬Squarefree a := by
  intro hs
  exact h.not_squarefree ((Nat.squarefree_mul ha.coprime_two_left).mpr ⟨Nat.prime_two.squarefree,hs⟩)

private theorem core_repeated_shape {a m : ℕ}
    (ha : Odd a) (hlen : a.primeFactorsList.length=3) (hns : ¬Squarefree a)
    (hm : m.primeFactorsList.length=4)
    (hgap : 2*a+12=m ∨ m+12=2*a)
    (hφ : (2*a).totient+m=m.totient+2*a) (hσ : σ 1 (2*a)+m=σ 1 m+2*a) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ Odd p ∧ Odd q ∧ a=p^2*q := by
  obtain ⟨p,q,hp,hq,hn⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hlen hns
  have hos := ha
  rw [hn] at hos
  simp only [pow_two,Nat.odd_mul] at hos
  have hpq : p ≠ q := by
    rintro rfl
    have h2p : p ≠ 2 := by have := Nat.odd_iff.mp hos.1.1; omega
    have hh : 2*a=p^3*2 := by rw [hn]; ring
    rw [hh] at hgap hφ hσ
    exact A056777.no_cube_prime_four_partner hp Nat.prime_two h2p hm hgap hφ hσ
  exact ⟨p,q,hp,hq,hpq,hos.1.1,hos.2,hn⟩

private theorem core_squarefree_shape {a : ℕ}
    (ha : Odd a) (hlen : a.primeFactorsList.length=3) (hs : Squarefree a) :
    ∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
      r≠s ∧ r≠t ∧ s≠t ∧ Odd r ∧ Odd s ∧ Odd t ∧ a=r*s*t := by
  have hprod := Nat.prod_primeFactorsList hs.ne_zero
  have hnd := hs.nodup_primeFactorsList
  obtain ⟨r,s,t,heq⟩ : ∃ r s t, a.primeFactorsList=[r,s,t] := by
    generalize hl : a.primeFactorsList = l at hlen ⊢
    rcases l with _ | ⟨r,l⟩
    · simp at hlen
    rcases l with _ | ⟨s,l⟩
    · simp at hlen
    rcases l with _ | ⟨t,l⟩
    · simp at hlen
    rcases l with _ | ⟨k,l⟩
    · exact ⟨r,s,t,rfl⟩
    · simp at hlen
  have hr := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=r) (by simp [heq])
  have hsp := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=s) (by simp [heq])
  have ht := Nat.prime_of_mem_primeFactorsList (n:=a) (p:=t) (by simp [heq])
  simp only [heq,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hnd
  have hform : a=r*s*t := by simpa [heq,mul_assoc] using hprod.symm
  rw [hform] at ha
  simp only [Nat.odd_mul] at ha
  exact ⟨r,s,t,hr,hsp,ht,hnd.1.1,hnd.1.2,hnd.2,ha.1.1,ha.1.2,ha.2,hform⟩

/-- No even endpoints with four prime factors each can satisfy the A056777 jump conditions. -/
theorem no_even_four_four_pair {n m : ℕ} (he : Even n)
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  have hs := A056777FourFour.remaining_four_four_shapes hn hm hgap hφ hσ
  by_cases hn4 : 4 ∣ n
  · have hm4 : 4 ∣ m := by omega
    have han : Squarefree n ∨ A056777FourFour.RepeatedFour n := by
      rcases hs with h|h|h
      · exact Or.inr h.1
      · exact Or.inr h.1
      · exact Or.inl h.1
    have ham : Squarefree m ∨ A056777FourFour.RepeatedFour m := by
      rcases hs with h|h|h
      · exact Or.inr h.2
      · exact Or.inl h.2
      · exact Or.inr h.2
    have hsn := seven_dvd_sigma_of_four_dvd han hn4
    have hsm := seven_dvd_sigma_of_four_dvd ham hm4
    omega
  have hme : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
  obtain ⟨a,ha⟩ := he
  obtain ⟨b,hb⟩ := hme
  have hna : n=2*a := by omega
  have hmb : m=2*b := by omega
  have hoa : Odd a := Nat.odd_iff.mpr (by omega)
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have ha0 : a≠0 := by have := Nat.odd_iff.mp hoa; omega
  have hb0 : b≠0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length=3 := by
    rw [hna,length_mul_two ha0] at hn
    omega
  have hbl : b.primeFactorsList.length=3 := by
    rw [hmb,length_mul_two hb0] at hm
    omega
  have hcore :
      (a+6=b ∧ b.totient=a.totient+12 ∧ σ 1 b=σ 1 a+4) ∨
      (b+6=a ∧ a.totient=b.totient+12 ∧ σ 1 a=σ 1 b+4) := by
    have hca := hoa.coprime_two_left
    have hcb := hob.coprime_two_left
    rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hφ
    norm_num at hφ
    rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
      isMultiplicative_sigma.map_mul_of_coprime hcb,show σ 1 2=3 by decide] at hσ
    omega
  have har (h : A056777FourFour.RepeatedFour n) :=
    core_repeated_shape hoa hal (core_nonsquarefree hoa (hna ▸ h)) hm
      (hna ▸ hgap) (hna ▸ hφ) (hna ▸ hσ)
  have hbr (h : A056777FourFour.RepeatedFour m) :=
    core_repeated_shape hob hbl (core_nonsquarefree hob (hmb ▸ h)) hn
      (hmb ▸ hgap.symm) (hmb ▸ hφ.symm) (hmb ▸ hσ.symm)
  rcases hs with ⟨han,hbn⟩ | ⟨han,hbn⟩ | ⟨han,hbn⟩
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,ha'⟩ := har han
    obtain ⟨r,s,hr,hs,hrs,hor,hos,hb'⟩ := hbr hbn
    rw [ha',hb'] at hcore
    rcases hcore with ⟨hg,hφ',hσ'⟩ | ⟨hg,hφ',hσ'⟩
    · exact no_odd_repeated_cores hp hq hr hs hpq hrs hop hoq hor hos hg hφ' hσ'
    · exact no_odd_repeated_cores hr hs hp hq hrs hpq hor hos hop hoq hg hφ' hσ'
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,ha'⟩ := har han
    have hfree : Squarefree b := (hmb ▸ hbn).squarefree_of_dvd (dvd_mul_left b 2)
    obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hor,hos,hot,hb'⟩ :=
      core_squarefree_shape hob hbl hfree
    rw [ha',hb'] at hcore
    exact no_odd_mixed_cores hp hq hr hs ht hpq hrs hrt hst hop hoq hor hos hot hcore
  · obtain ⟨p,q,hp,hq,hpq,hop,hoq,hb'⟩ := hbr hbn
    have hfree : Squarefree a := (hna ▸ han).squarefree_of_dvd (dvd_mul_left a 2)
    obtain ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hor,hos,hot,ha'⟩ :=
      core_squarefree_shape hoa hal hfree
    rw [ha',hb'] at hcore
    exact no_odd_mixed_cores hp hq hr hs ht hpq hrs hrt hst hop hoq hor hos hot hcore.symm

/-- Every remaining 4×4 candidate is odd at both endpoints, and at least one endpoint is
a square times two other distinct primes. -/
theorem odd_four_four_residual {n m : ℕ}
    (hn : n.primeFactorsList.length=4) (hm : m.primeFactorsList.length=4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    Odd n ∧ Odd m ∧
      ((A056777FourFour.RepeatedFour n ∧ A056777FourFour.RepeatedFour m) ∨
        (A056777FourFour.RepeatedFour n ∧ Squarefree m) ∨
        (Squarefree n ∧ A056777FourFour.RepeatedFour m)) := by
  have hnodd := Nat.not_even_iff_odd.mp
    (fun he => no_even_four_four_pair he hn hm hgap hφ hσ)
  have hmod := Nat.odd_iff.mp hnodd
  exact ⟨hnodd,Nat.odd_iff.mpr (by omega),
    A056777FourFour.remaining_four_four_shapes hn hm hgap hφ hσ⟩

end A056777EvenFourFour

#print axioms A056777EvenFourFour.no_even_four_four_pair
#print axioms A056777EvenFourFour.odd_four_four_residual
