import A056777FourFour
import A056777RepeatedTriple
import A056777Parity
import A056777SquarefreeFiveMoments
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777ThreeSquarefreeFive

private theorem squarefree_five_shape {m : ℕ} (hm : m.primeFactorsList.length=5)
    (hs : Squarefree m) :
    ∃ a b c d e : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧ e.Prime ∧
      a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ b≠c ∧ b≠d ∧ b≠e ∧
      c≠d ∧ c≠e ∧ d≠e ∧ m=a*b*c*d*e := by
  obtain ⟨a,b,c,d,e,he⟩ : ∃ a b c d e, m.primeFactorsList=[a,b,c,d,e] := by
    generalize hl : m.primeFactorsList = l at hm ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at hm
    rcases l with _ | ⟨b,l⟩
    · simp at hm
    rcases l with _ | ⟨c,l⟩
    · simp at hm
    rcases l with _ | ⟨d,l⟩
    · simp at hm
    rcases l with _ | ⟨e,l⟩
    · simp at hm
    rcases l with _ | ⟨f,l⟩
    · exact ⟨a,b,c,d,e,rfl⟩
    · simp at hm
  have ha := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=c) (by simp [he])
  have hd := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=d) (by simp [he])
  have hp := Nat.prime_of_mem_primeFactorsList (n:=m) (p:=e) (by simp [he])
  have hn := hs.nodup_primeFactorsList
  simp only [he,List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at hn
  have hf := (Nat.prod_primeFactorsList hs.ne_zero).symm
  exact ⟨a,b,c,d,e,ha,hb,hc,hd,hp,hn.1.1,hn.1.2.1,hn.1.2.2.1,hn.1.2.2.2,
    hn.2.1.1,hn.2.1.2.1,hn.2.1.2.2,hn.2.2.1.1,hn.2.2.1.2,hn.2.2.2,
    by simpa [he,mul_assoc] using hf⟩

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p=p+1 := by
  simpa using sigma_one_apply_prime_pow (i:=1) hp

private theorem quintic_formulas {a b c d e : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime) (he : e.Prime)
    (hab : a≠b) (hac : a≠c) (had : a≠d) (hae : a≠e) (hbc : b≠c) (hbd : b≠d)
    (hbe : b≠e) (hcd : c≠d) (hce : c≠e) (hde : d≠e) :
    (σ 1 (a*b*c*d*e)+(a*b*c*d*e).totient =
      2*(a*b*c*d*e)+2*(a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+
        b*c*d+b*c*e+b*d*e+c*d*e+a+b+c+d+e)) ∧
    ((a*b*c*d*e).totient+(a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e)+
        (a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e)+1 =
      a*b*c*d*e+(a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e)+
        (a+b+c+d+e)) := by
  have h₁ := (Nat.coprime_primes ha hb).mpr hab
  have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
  have h₃ := (((Nat.coprime_primes ha hd).mpr had).mul_left
    ((Nat.coprime_primes hb hd).mpr hbd)).mul_left ((Nat.coprime_primes hc hd).mpr hcd)
  have h₄ := ((((Nat.coprime_primes ha he).mpr hae).mul_left
    ((Nat.coprime_primes hb he).mpr hbe)).mul_left ((Nat.coprime_primes hc he).mpr hce)).mul_left
      ((Nat.coprime_primes hd he).mpr hde)
  rw [Nat.totient_mul h₄,Nat.totient_mul h₃,Nat.totient_mul h₂,Nat.totient_mul h₁,
    Nat.totient_prime ha,Nat.totient_prime hb,Nat.totient_prime hc,Nat.totient_prime hd,
    Nat.totient_prime he,isMultiplicative_sigma.map_mul_of_coprime h₄,
    isMultiplicative_sigma.map_mul_of_coprime h₃,isMultiplicative_sigma.map_mul_of_coprime h₂,
    isMultiplicative_sigma.map_mul_of_coprime h₁,sigma_prime ha,sigma_prime hb,sigma_prime hc,
    sigma_prime hd,sigma_prime he]
  have ha1 := ha.pos
  have hb1 := hb.pos
  have hc1 := hc.pos
  have hd1 := hd.pos
  have he1 := he.pos
  zify [ha1,hb1,hc1,hd1,he1]
  constructor <;> ring

private theorem cube_excess {p : ℕ} (hp : p.Prime) :
    σ 1 (p^3)+(p^3).totient=2*p^3+p+1 := by
  have hσ : σ 1 (p^3)=1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  rw [hσ,show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
  have hp1 := hp.pos
  zify [hp1]
  ring

private theorem product_three_far_below_cube {p a b c : ℕ} (hp : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) : a*b*c+12 < p^3 := by
  have h₁ : a ≤ p-1 := by omega
  have h₂ : b ≤ p-1 := by omega
  have h₃ : c ≤ p-1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
  have hp₁ : 1 ≤ p := by omega
  zify [hp₁] at hprod hp ⊢
  have hh : 9 ≤ (p : ℤ)*p := calc
    9 = (3 : ℤ)*3 := by decide
    _ ≤ _ := mul_le_mul hp hp (by decide) (by omega)
  have hq := mul_nonneg (show 0 ≤ (p : ℤ) by omega) (show 0 ≤ (p : ℤ)-3 by omega)
  nlinarith only [hprod,hh,hq]

/-- A prime cube cannot be paired with a squarefree five-factor endpoint. -/
theorem no_cube_squarefree_five_pair {p m : ℕ}
    (hp : p.Prime) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : p^3+12=m ∨ m+12=p^3)
    (hφ : (p^3).totient+m=m.totient+p^3) (hσ : σ 1 (p^3)+m=σ 1 m+p^3) : False := by
  by_cases hp2 : p=2
  · subst p
    have ht : 4 ∣ m := by norm_num at hgap; omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) ht
  have hp3 : 3≤p := by have := hp.two_le; omega
  obtain ⟨a,b,c,d,e,ha,hb,hc,hd,he,hab,hac,had,hae,hbc,hbd,hbe,hcd,hce,hde,rfl⟩ :=
    squarefree_five_shape hm hs
  have hq := (quintic_formulas ha hb hc hd he hab hac had hae hbc hbd hbe hcd hce hde).1
  have hpc := cube_excess hp
  have hlt1 : a*b*c < p := by omega
  have hlt2 : d*e < p := by
    have ha1 : 1≤a := ha.pos
    have ht := Nat.mul_le_mul_right (d*e) ha1
    simp only [one_mul] at ht
    have hprod : a*(d*e)=a*d*e := by ring
    rw [hprod] at ht
    omega
  have hlt := product_three_far_below_cube hp3 hlt1 hlt2 (show 1<p by omega)
  have hf : a*b*c*d*e=(a*b*c)*(d*e)*1 := by ring
  rw [hf] at hgap
  omega

/-- With a squarefree five-factor partner, a three-factor endpoint must be odd
and of the form p²q with two distinct odd primes. -/
theorem remaining_three_squarefree_five {n m : ℕ}
    (hn : n.primeFactorsList.length=3) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ Odd p ∧ Odd q ∧ Odd m ∧ n=p^2*q := by
  have hn0 : n≠0 := by rintro rfl; simp at hn
  have hns : ¬Squarefree n := by
    intro hfree
    have hc {x : ℕ} (hsx : Squarefree x) (hx : 3≤x.primeFactorsList.length) :
        3≤x.primeFactors.card := by
      rwa [← Nat.toFinset_factors,List.toFinset_card_of_nodup hsx.nodup_primeFactorsList]
    by_cases he : Even n
    · have hmE : Even m := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
      have hg' := hgap
      rcases hg' with h|h
      · rw [← h] at hs hφ hσ
        exact A056777Squarefree.no_even_squarefree_pair he hfree hs (by omega) (by omega)
      · rw [← h] at hfree hφ hσ
        exact A056777Squarefree.no_even_squarefree_pair hmE hs hfree (by omega) (by omega)
    · have ho := Nat.not_even_iff_odd.mp he
      have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
      exact A056777FourFour.no_odd_three_distinct_pair ho hom (hc hfree (by omega)) (hc hs (by omega))
        hgap hφ
  obtain ⟨p,q,hp,hq,hform⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hn hns
  have hpq : p≠q := by
    rintro rfl
    have hf : n=p^3 := by rw [hform]; ring
    rw [hf] at hgap hφ hσ
    exact no_cube_squarefree_five_pair hp hm hs hgap hφ hσ
  have hp2 : p≠2 := by
    rintro rfl
    have hdm : 4∣m := by
      have hn4 : 4∣n := hform ▸ (dvd_mul_right ((2:ℕ)^2) q)
      omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) hdm
  have hq2 : q≠2 := by
    rintro rfl
    have hshape : ∃ p:ℕ, n=2*p^2 := ⟨p,by rw [hform,mul_comm]⟩
    rcases hgap with hh|hh
    · have hstep : σ 1 (n+12)=σ 1 n+12 := by rw [hh]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).1 (Or.inr hshape)
    · have hstep : σ 1 (m+12)=σ 1 m+12 := by rw [hh]; omega
      obtain ⟨p,hp'⟩ := hshape
      exact (A056777Parity.no_square_shapes_of_sigma_step hs.ne_zero hstep).2
        (Or.inr ⟨p,hh.trans hp'⟩)
  have hop : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hoq : Odd q := hq.eq_two_or_odd'.resolve_left hq2
  have hon : Odd n := by rw [hform]; exact (hop.pow).mul hoq
  have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hon; omega)
  exact ⟨p,q,hp,hq,hpq,hop,hoq,hom,hform⟩

private theorem squarefree_four_large_totient_defect {m : ℕ}
    (hm : m.primeFactorsList.length=4) (hs : Squarefree m) :
    m.totient+8≤m := by
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | ⟨p,q,hp,hq,hne,he⟩ |
    ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr,he⟩ | ⟨a,b,c,d,ha,hb,hc,hd,hab,hac,had,hbc,hbd,hcd,rfl⟩
  · have hD : k*k∣m := by rw [hk,pow_two]
    have hk1 := Nat.isUnit_iff.mp (hs k hD)
    simp [hk,hk1] at hm
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs p hp) ⟨p*q,by rw [he]; ring⟩).elim
  · exact ((Nat.squarefree_iff_prime_squarefree.mp hs p hp) ⟨q*r,by rw [he]; ring⟩).elim
  · have h₁ := (Nat.coprime_primes ha hb).mpr hab
    have h₂ := ((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc)
    have h₃ := (((Nat.coprime_primes ha hd).mpr had).mul_left
      ((Nat.coprime_primes hb hd).mpr hbd)).mul_left ((Nat.coprime_primes hc hd).mpr hcd)
    rw [Nat.totient_mul h₃,Nat.totient_mul h₂,Nat.totient_mul h₁,
      Nat.totient_prime ha,Nat.totient_prime hb,Nat.totient_prime hc,Nat.totient_prime hd]
    have hbnd := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (le_refl (a-1))
      (Nat.sub_le b 1)) (Nat.sub_le c 1)) (Nat.sub_le d 1)
    have h8 := Nat.mul_le_mul (Nat.mul_le_mul hb.two_le hc.two_le) hd.two_le
    have ha1 := ha.pos
    zify [ha1] at hbnd h8 ⊢
    nlinarith only [hbnd,h8]

private theorem no_base_three_squarefree_five {q m : ℕ}
    (hq : q.Prime) (hq3 : q≠3) (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : 3^2*q+12=m ∨ m+12=3^2*q)
    (hφ : (3^2*q).totient+m=m.totient+3^2*q) : False := by
  have hm3 : 3∣m := by norm_num at hgap; omega
  obtain ⟨M,hM⟩ := hm3
  have hms : Squarefree (3*M) := hM ▸ hs
  have hM0 : M≠0 := fun h => hs.ne_zero (by simp [hM,h])
  have hcop := Nat.coprime_of_squarefree_mul hms
  have hMfree := hms.squarefree_of_dvd (dvd_mul_left M 3)
  have hal := (Nat.perm_primeFactorsList_mul (by decide : (3:ℕ)≠0) hM0).length_eq
  rw [← hM,Nat.primeFactorsList_prime Nat.prime_three,
    List.length_append,List.length_singleton,hm] at hal
  have hbig := squarefree_four_large_totient_defect (by omega : M.primeFactorsList.length=4) hMfree
  have hc := ((Nat.coprime_primes Nat.prime_three hq).mpr hq3.symm).pow_left 2
  rw [hM,Nat.totient_mul hc,Nat.totient_mul hcop,
    show ((3:ℕ)^2).totient=6 by decide,Nat.totient_prime hq,Nat.totient_prime Nat.prime_three] at hφ
  rw [hM] at hgap
  norm_num at hφ hgap
  have := hq.two_le
  omega

/-- The residual odd p²q endpoint for a squarefree five-factor partner
has the indicated two residue classes and a repeated prime of at least seven. -/
theorem three_squarefree_five_residues {p q m : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hop : Odd p) (hoq : Odd q) (hom : Odd m)
    (hm : m.primeFactorsList.length=5) (hs : Squarefree m)
    (hgap : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q) (hσ : σ 1 (p^2*q)+m=σ 1 m+p^2*q) :
    7≤p ∧ p%4=3 ∧ q%8=3 := by
  have hcard : 3≤m.primeFactors.card := by
    rw [← Nat.toFinset_factors,List.toFinset_card_of_nodup hs.nodup_primeFactorsList,hm]
    decide
  have hdφ : 8∣m.totient := (pow_dvd_pow 2 hcard).trans
    (A056777OddFour.two_pow_card_dvd_totient hom)
  have hfilt : (m.primeFactors.filter fun x => x≠2 ∧ Odd (m.factorization x)) = m.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have ⟨hxP,hxD,hx0⟩ := Nat.mem_primeFactors.mp hx
    have hx2 : x≠2 := by
      rintro rfl
      have := Nat.odd_iff.mp hom
      omega
    have hx1 := hxP.factorization_pos_of_dvd hx0 hxD
    have hxle := hs.natFactorization_le_one x
    have he : m.factorization x=1 := by omega
    exact ⟨hx2,he ▸ (by decide : Odd 1)⟩
  have hdσ := A056777Squarefree.two_pow_card_odd_exponents_dvd_sigma hs.ne_zero
  rw [hfilt] at hdσ
  have hdσ' : 8∣σ 1 m := (pow_dvd_pow 2 hcard).trans hdσ
  have hc := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hφp : (p^2).totient=p*(p-1) := by simpa using Nat.totient_prime_pow_succ hp 1
  have hσp : σ 1 (p^2)=1+p+p^2 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hp3 : p≠3 := by
    rintro rfl
    exact no_base_three_squarefree_five hq hpq.symm hm hs hgap hφ
  rw [Nat.totient_mul hc,hφp,Nat.totient_prime hq] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hc,hσp,sigma_prime hq] at hσ
  have hpo := Nat.odd_iff.mp hop
  have hqo := Nat.odd_iff.mp hoq
  have hnd : ¬8∣p*(p-1)*(q-1) := by omega
  have hp4 : p%4=3 := by
    by_contra h
    have hpD : 4∣p-1 := by omega
    have hqD : 2∣q-1 := by omega
    exact hnd (mul_dvd_mul (dvd_mul_of_dvd_right hpD p) hqD)
  have hq4 : q%4=3 := by
    by_contra h
    have hpD : 2∣p-1 := by omega
    have hqD : 4∣q-1 := by omega
    exact hnd (mul_dvd_mul (dvd_mul_of_dvd_right hpD p) hqD)
  have hq8 : q%8=3 := by
    by_contra h
    have hd : 8∣q+1 := by omega
    have hh := dvd_mul_of_dvd_right hd (1+p+p^2)
    omega
  exact ⟨by omega,hp4,hq8⟩

private theorem distinct_odd_pair_ge_fifteen {a b : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hoa : Odd a) (hob : Odd b) (hne : a≠b) :
    15≤a*b := by
  have ha2 := ha.two_le
  have hb2 := hb.two_le
  have haO := Nat.odd_iff.mp hoa
  have hbO := Nat.odd_iff.mp hob
  by_cases h : a=3
  · exact Nat.mul_le_mul (by omega : 3≤a) (by omega : 5≤b)
  · exact Nat.mul_le_mul (by omega : 5≤a) (by omega : 3≤b)

private theorem quintic_moment_bounds (a b c d e : ℤ)
    (ha : 3≤a) (hb : 3≤b) (hc : 3≤c) (hd : 3≤d) (he : 3≤e)
    (hab : 15≤a*b) (hac : 15≤a*c) (had : 15≤a*d) (hae : 15≤a*e) (hbc : 15≤b*c) (hbd : 15≤b*d) (hbe : 15≤b*e) (hcd : 15≤c*d) (hce : 15≤c*e) (hde : 15≤d*e) :
    let A := a+b+c+d+e
    let E := a*b+a*c+a*d+a*e+b*c+b*d+b*e+c*d+c*e+d*e
    let X := a*b*c+a*b*d+a*b*e+a*c*d+a*c*e+a*d*e+b*c*d+b*c*e+b*d*e+c*d*e
    let Y := a*b*c*d+a*b*c*e+a*b*d*e+a*c*d*e+b*c*d*e
    let Z := a*b*c*d*e
    30*A≤X ∧ A≤E ∧ Z^3≤X^5 ∧ 5*X*Z≤2*Y^2 := by
  intro A E X Y Z
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [A,X]
    have ha' := mul_nonneg (show 0≤a by omega) (show 0≤b*c + b*d + b*e + c*d + c*e + d*e-90 by omega)
    have hb' := mul_nonneg (show 0≤b by omega) (show 0≤a*c + a*d + a*e + c*d + c*e + d*e-90 by omega)
    have hc' := mul_nonneg (show 0≤c by omega) (show 0≤a*b + a*d + a*e + b*d + b*e + d*e-90 by omega)
    have hd' := mul_nonneg (show 0≤d by omega) (show 0≤a*b + a*c + a*e + b*c + b*e + c*e-90 by omega)
    have he' := mul_nonneg (show 0≤e by omega) (show 0≤a*b + a*c + a*d + b*c + b*d + c*d-90 by omega)
    nlinarith only [ha',hb',hc',hd',he']
  · dsimp [A,E]
    have h₁ := mul_nonneg (show 0≤a-2 by omega) (show 0≤b-1 by omega)
    have h₂ := mul_nonneg (show 0≤c-2 by omega) (show 0≤d-1 by omega)
    have h₃ := mul_nonneg (show 0≤a-1 by omega) (show 0≤e by omega)
    nlinarith only [h₁,h₂,h₃,hb,hd,hac,had,hbc,hbd,hbe,hce,hde]
  · have ha0 : 0≤a := by omega
    have hb0 : 0≤b := by omega
    have hc0 : 0≤c := by omega
    have hd0 : 0≤d := by omega
    have he0 : 0≤e := by omega
    have hX0 : 0≤X := by dsimp [X]; positivity
    have habc : 0≤a*b*c := by positivity
    have habd : 0≤a*b*d := by positivity
    have habe : 0≤a*b*e := by positivity
    have hacd : 0≤a*c*d := by positivity
    have hace : 0≤a*c*e := by positivity
    have hade : 0≤a*d*e := by positivity
    have hbcd : 0≤b*c*d := by positivity
    have hbce : 0≤b*c*e := by positivity
    have hbde : 0≤b*d*e := by positivity
    have hcde : 0≤c*d*e := by positivity
    have htabc : a*b*c≤X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htbcd : b*c*d≤X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htcde : c*d*e≤X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htade : a*d*e≤X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have htabe : a*b*e≤X := by dsimp [X]; linarith only [habc,habd,habe,hacd,hace,hade,hbcd,hbce,hbde,hcde]
    have h₁ := mul_le_mul htabc htbcd habc hX0
    have h₂ := mul_le_mul h₁ htcde hcde (mul_nonneg hX0 hX0)
    have h₃ := mul_le_mul h₂ htade hade (by positivity : 0≤X*X*X)
    have h₄ := mul_le_mul h₃ htabe habe (by positivity : 0≤X*X*X*X)
    dsimp [Z]
    nlinarith only [h₄]
  · dsimp [X,Y,Z]
    nlinarith only [sq_nonneg (a*b*c*d-a*b*c*e),
      sq_nonneg (a*b*c*d-a*b*d*e),
      sq_nonneg (a*b*c*d-a*c*d*e),
      sq_nonneg (a*b*c*d-b*c*d*e),
      sq_nonneg (a*b*c*e-a*b*d*e),
      sq_nonneg (a*b*c*e-a*c*d*e),
      sq_nonneg (a*b*c*e-b*c*d*e),
      sq_nonneg (a*b*d*e-a*c*d*e),
      sq_nonneg (a*b*d*e-b*c*d*e),
      sq_nonneg (a*c*d*e-b*c*d*e)]

end A056777ThreeSquarefreeFive

#print axioms A056777ThreeSquarefreeFive.no_cube_squarefree_five_pair
#print axioms A056777ThreeSquarefreeFive.remaining_three_squarefree_five

#print axioms A056777ThreeSquarefreeFive.three_squarefree_five_residues
