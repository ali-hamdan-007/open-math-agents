import A056777EvenRepeatedThreeFive

open scoped ArithmeticFunction.sigma

namespace A056777OddRepeatedThreeFive

/-- An odd square times a distinct prime cannot pair with a prime fifth power.
The totient jump alone excludes this case. -/
theorem no_square_prime_fifth_power {p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpo : Odd p) (hpq : p≠q)
    (hg : p^2*q+12=r^5 ∨ r^5+12=p^2*q)
    (hφ : (p^2*q).totient+r^5=(r^5).totient+p^2*q) : False := by
  have hF := (A056777EvenFourFour.square_prime_formulas hp hq hpq).1
  have hF' : (r^5).totient+r^4=r^5 := by
    rw [show (r^5).totient=r^4*(r-1) from Nat.totient_prime_pow_succ hr 4]
    have hr1 := hr.pos
    zify [hr1]
    ring
  have he : p*(p+q-1)=r^4 := by omega
  have hd : p∣r^4 := ⟨p+q-1,he.symm⟩
  have hpr : p=r := (Nat.dvd_prime hr).mp (hp.dvd_of_dvd_pow hd) |>.resolve_left hp.ne_one
  subst r
  have HH : p*(p+q-1)=p*p^3 := he.trans (by ring)
  have hq' : p+q-1=p^3 := Nat.eq_of_mul_eq_mul_left hp.pos HH
  have hp1 := hp.pos
  have HP : p^5=p^2*q+p^2*(p-1) := by
    have hh : p+q=p^3+1 := by omega
    zify [hp1]
    have hhz : (p:ℤ)+(q:ℤ)=(p:ℤ)^3+1 := by exact_mod_cast hh
    nlinarith only [congrArg (fun x : ℤ => (p:ℤ)^2*x) hhz]
  have hp3 : 3≤p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
  have hbound : 18≤p^2*(p-1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hp3 2) (by omega : 2≤p-1)
  omega

open Nat ArithmeticFunction
open A056777EvenRepeatedThreeFive (phi_lower_defect four_odd_core)

private theorem core_length {k u : ℕ} (hu : Odd u)
    (hm : (3^k*u).primeFactorsList.length=5) :
    k+u.primeFactorsList.length=5 := by
  have hu0 : u≠0 := by have := Nat.odd_iff.mp hu; omega
  have hh := (Nat.perm_primeFactorsList_mul
    (pow_ne_zero k (by decide : (3:ℕ)≠0)) hu0).length_eq
  simpa [hm,Nat.prime_three.primeFactorsList_pow] using hh.symm

private theorem three_core_phi {k u : ℕ} (hk : 0<k) (hu : ¬3∣u) :
    (3^k*u).totient=2*3^(k-1)*u.totient := by
  have hc := (Nat.coprime_or_dvd_of_prime Nat.prime_three u).resolve_right hu
  rw [Nat.totient_mul (hc.pow_left k),Nat.totient_prime_pow Nat.prime_three hk]
  norm_num [mul_comm]

private theorem no_shared_three_at_square {q m : ℕ} (hq : q.Prime) (hqo : Odd q) (hq3 : q≠3)
    (hm : m.primeFactorsList.length=5) (h3m : 3∣m)
    (hg : 9*q+12=m ∨ m+12=9*q)
    (hφ : (9*q).totient+m=m.totient+9*q) : False := by
  obtain ⟨u,hu⟩ := h3m
  have hu3 : ¬3∣u := by
    rintro ⟨t,ht⟩
    rw [hu,ht] at hg
    omega
  have huo := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hqo; omega : u%2=1)
  have hL := core_length (k:=1) huo (by simpa [hu] using hm)
  obtain ⟨hlarge,hpow⟩ := four_odd_core huo (by omega : u.primeFactorsList.length=4)
  have hmφ := three_core_phi (k:=1) (by decide) hu3
  have hf := (A056777EvenFourFour.square_prime_formulas Nat.prime_three hq (Ne.symm hq3)).1
  norm_num at hmφ hf
  rw [hu,hmφ] at hφ
  have hb : u-u.totient≤5 := by omega
  have H := Nat.pow_le_pow_left hb 4
  have J := Nat.pow_le_pow_left hlarge 3
  omega

private theorem no_shared_three_at_single {p m : ℕ} (hp : p.Prime) (hpo : Odd p) (hp3 : p≠3)
    (hm : m.primeFactorsList.length=5) (h3m : 3∣m)
    (hg : p^2*3+12=m ∨ m+12=p^2*3)
    (hφ : (p^2*3).totient+m=m.totient+p^2*3) : False := by
  have hm0 : m≠0 := by rintro rfl; simp at hm
  obtain ⟨k,u,hu3,hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by decide)
  have hk : k≠0 := by rintro rfl; apply hu3; simpa [hmu] using h3m
  have huO : Odd u := by
    have hmO : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp (hpo.pow (n:=2)); omega)
    exact (Nat.odd_mul.mp (hmu ▸ hmO)).2
  have hL := core_length huO (by simpa [hmu] using hm)
  have hM := three_core_phi (Nat.pos_of_ne_zero hk) hu3
  have hF := (A056777EvenFourFour.square_prime_formulas hp Nat.prime_three hp3).1
  have hp1 := hp.pos
  have hp5 : 5≤p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
  have hpdiv : ¬3∣p := fun h => hp3 ((Nat.dvd_prime hp).mp h |>.resolve_left (by decide)).symm
  have hpmod : p^2%3=1 := by
    have hh := Nat.pow_mod p 2 3
    have hne : p%3≠0 := by simpa [Nat.dvd_iff_mod_eq_zero] using hpdiv
    have ht : p%3=1 ∨ p%3=2 := by omega
    rcases ht with h|h <;> norm_num [h] at hh <;> omega
  rw [hmu,hM] at hφ
  rw [hmu] at hg
  by_cases hk1 : k=1
  · subst k
    norm_num at hg hφ
    have hup : u=p^2+4 := by
      by_contra hn
      apply hu3
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    obtain ⟨_,hpow⟩ := four_odd_core huO (by omega : u.primeFactorsList.length=4)
    have hE : p*(p+3-1)=p^2+2*p := by rw [show p+3-1=p+2 by omega]; ring
    have hbound : u-u.totient≤p := by omega
    have hJ := Nat.pow_le_pow_left hbound 4
    have hKill : p^4<(p^2)^3 := by
      have H := Nat.mul_lt_mul_of_pos_left (show 1<p^2 by nlinarith) (pow_pos hp1 4)
      simpa [show p^4*p^2=(p^2)^3 by ring] using H
    have hPP : (p^2)^3≤u^3 := Nat.pow_le_pow_left (by omega) 3
    omega
  · have hcase : k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
    let C := 3^(k-1)
    have hC3 : 3∣C := by
      have H : 1≤k-1 := by omega
      exact pow_dvd_pow 3 H
    have hC0 : 0<C := by positivity
    have hC : 3^k=3*C := by
      dsimp [C]
      conv_lhs => rw [show k=k-1+1 by omega,pow_succ,mul_comm]
    rw [hC] at hg hφ
    change _ + _ = 2*C*u.totient + _ at hφ
    rw [show 3*C*u=3*(C*u) by ring,show 2*C*u.totient=2*(C*u.totient) by ring] at hφ
    have hcore : C*u+4=p^2 := by
      have h3Cu : 3∣C*u := hC3.trans (dvd_mul_right _ _)
      rw [Nat.dvd_iff_mod_eq_zero] at h3Cu
      have hge : p^2+4=C*u ∨ C*u+4=p^2 := by
        have he : 3*C*u=3*(C*u) := by ring
        rw [he] at hg
        omega
      omega
    have hE : p*(p+3-1)=p^2+2*p := by rw [show p+3-1=p+2 by omega]; ring
    have hdef : C*(u-u.totient)=p+2 := by
      have htu := Nat.totient_le u
      rw [Nat.mul_sub_left_distrib]
      omega
    let v := u-u.totient
    have hv : C*v=p+2 := hdef
    have hu' : u=(p-2)*v := by
      apply Nat.eq_of_mul_eq_mul_left hC0
      calc
        C*u = p^2-4 := by omega
        _ = (p-2)*(p+2) := by zify [show 4≤p^2 by nlinarith,show 2≤p by omega]; ring
        _ = C*((p-2)*v) := by rw [←hv]; ring
    have hv1 : v=1 := by
      have hv0 : 0<v := by by_contra! h; simp [show v=0 by omega] at hv
      by_contra h
      obtain ⟨r,hr,⟨w,hw⟩⟩ := Nat.exists_prime_and_dvd (show v≠1 from h)
      have he : u=r*((p-2)*w) := by rw [hu',hw]; ring
      have hdefr := phi_lower_defect (u:=(p-2)*w) hr
      rw [←he] at hdefr
      have hw0 : 1≤w := by by_contra! h; simp [show w=0 by omega] at hw; omega
      have HB := Nat.mul_le_mul_left (p-2) hw0
      have HC : 3*v≤p+2 := (Nat.mul_le_mul_right _ (Nat.le_of_dvd hC0 hC3)).trans_eq hv
      have : v < p-2 := by omega
      dsimp [v] at this
      omega
    rw [hv1,mul_one] at hv
    rcases hcase with rfl|rfl|rfl|rfl
    · norm_num [C] at hv
      omega
    · norm_num [C] at hv
      have hP : p=7 := by omega
      subst p
      have hU : u=5 := by norm_num [hv1] at hu'; exact hu'
      rw [hU] at hL
      rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hL
      simp at hL
    · norm_num [C] at hv
      have hP : p=25 := by omega
      subst p
      exact (by decide : ¬Nat.Prime 25) hp
    · norm_num [C] at hv
      have hP : p=79 := by omega
      subst p
      have hU : u=77 := by norm_num [hv1] at hu'; exact hu'
      rw [hU] at hL
      have hf77 := (Nat.perm_primeFactorsList_mul
        (by decide : (7:ℕ)≠0) (by decide : (11:ℕ)≠0)).length_eq
      rw [Nat.primeFactorsList_prime (by decide : Nat.Prime 7),
        Nat.primeFactorsList_prime (by decide : Nat.Prime 11)] at hf77
      change (77:ℕ).primeFactorsList.length=2 at hf77
      omega

/-- Any odd square-prime endpoint in a three-versus-five pair is coprime to its partner. -/
theorem coprime_square_prime_five {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p≠q) (hm : m.primeFactorsList.length=5)
    (hg : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q) : (p^2*q).Coprime m := by
  rw [Nat.coprime_mul_iff_left]
  have neither {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrn : r∣p^2*q) : r∣m → r=3 := by
    intro hrm
    have hd : r∣12 := by
      rcases hg with h|h
      · exact (Nat.dvd_add_iff_right hrn).mpr (by rwa [h])
      · exact (Nat.dvd_add_iff_right hrm).mpr (by rwa [h])
    have hd' : r∣2^2*3 := hd
    rcases hr.dvd_mul.mp hd' with h|h
    · have hr2 := (Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow h) |>.resolve_left hr.ne_one
      subst r
      have := Nat.odd_iff.mp hro
      omega
    · exact (Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hr.ne_one
  have hpn : p∣p^2*q := (dvd_pow_self p (by decide : 2≠0)).trans (dvd_mul_right _ _)
  have hqn : q∣p^2*q := dvd_mul_left _ _
  constructor
  · apply Nat.Coprime.pow_left
    refine (Nat.coprime_or_dvd_of_prime hp m).resolve_right fun h => ?_
    have h3 := neither hp hpo hpn h
    subst p
    exact no_shared_three_at_square hq hqo (Ne.symm hpq) hm h hg hφ
  · refine (Nat.coprime_or_dvd_of_prime hq m).resolve_right fun h => ?_
    have h3 := neither hq hqo hqn h
    subst q
    exact no_shared_three_at_single hp hpo hpq hm h hg hφ

/-- Every divisor shared by the larger-factor-count endpoint and its totient divides
the sum of the two prime bases of the three-factor endpoint, minus one. -/
theorem common_totient_divisor_square_prime_five {p q m d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hpq : p≠q) (hm : m.primeFactorsList.length=5)
    (hg : p^2*q+12=m ∨ m+12=p^2*q)
    (hφ : (p^2*q).totient+m=m.totient+p^2*q)
    (hdm : d∣m) (hdφ : d∣m.totient) :
    d∣p+q-1 ∧ d∣(p^2*(p-1)+12) * (p^2*(p-1)-12) := by
  have hc := coprime_square_prime_five hp hq hpo hqo hpq hm hg hφ
  have hpd : p.Coprime d :=
    (hc.coprime_dvd_left ((dvd_pow_self p (by decide : 2≠0)).trans (dvd_mul_right _ _))).coprime_dvd_right hdm
  have hf := (A056777EvenFourFour.square_prime_formulas hp hq hpq).1
  have hdef : m=m.totient+p*(p+q-1) := by omega
  have hD : d∣p*(p+q-1) := (Nat.dvd_add_iff_right hdφ).mpr (hdef ▸ hdm)
  have hsum := hpd.symm.dvd_of_dvd_mul_left hD
  refine ⟨hsum,?_⟩
  have H : p^2*q+p^2*(p-1)=p^2*(p+q-1) := by
    rw [←Nat.mul_add]
    congr 1
    have := hp.pos
    omega
  have hdSum : d∣p^2*q+p^2*(p-1) := H ▸ dvd_mul_of_dvd_right hsum _
  rcases hg with h|h
  · have he : p^2*q+p^2*(p-1)=(p^2*q+12)+(p^2*(p-1)-12) := by
      have hp3 : 3≤p := by have := hp.two_le; have := Nat.odd_iff.mp hpo; omega
      have hge : 18≤p^2*(p-1) := Nat.mul_le_mul (Nat.pow_le_pow_left hp3 2) (by omega : 2≤p-1)
      omega
    rw [he,h] at hdSum
    exact dvd_mul_of_dvd_right ((Nat.dvd_add_iff_right hdm).mpr hdSum) _
  · have he : p^2*q+p^2*(p-1)=m+(p^2*(p-1)+12) := by omega
    rw [he] at hdSum
    exact dvd_mul_of_dvd_left ((Nat.dvd_add_iff_right hdm).mpr hdSum) _

end A056777OddRepeatedThreeFive

#print axioms A056777OddRepeatedThreeFive.no_square_prime_fifth_power

#print axioms A056777OddRepeatedThreeFive.coprime_square_prime_five

#print axioms A056777OddRepeatedThreeFive.common_totient_divisor_square_prime_five
