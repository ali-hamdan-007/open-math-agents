import A056777EvenSquarefreeThreeFive
import A056777CubeFive
import A056777OddSquarefreeThreeFiveMoments

open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace A056777EvenRepeatedThreeFive

private theorem len_mul {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa using (Nat.perm_primeFactorsList_mul ha hb).length_eq

theorem phi_lower_defect {r u : ℕ} (hr : r.Prime) :
    (r*u).totient+u ≤ r*u := by
  by_cases h : r∣u
  · obtain ⟨v,rfl⟩ := h
    rw [Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_right r v)]
    have haux : (r*v).totient ≤ (r-1)*v := by
      by_cases hd : r∣v
      · -- Prove the bound along the chain of powers of r.
        clear hd
        induction v using Nat.strong_induction_on with
        | h v ih =>
          by_cases hv : v=0
          · simp [hv]
          by_cases hd : r∣v
          · obtain ⟨w,rfl⟩ := hd
            have hw0 : 0<w := by by_contra! h; simp [show w=0 by omega] at hv
            have hlt : w<r*w := by nlinarith [hr.two_le]
            rw [Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_right r w)]
            calc
              r*(r*w).totient ≤ r*((r-1)*w) := Nat.mul_le_mul_left _ (ih w hlt)
              _ = (r-1)*(r*w) := by ring
          · rw [Nat.totient_mul_of_prime_of_not_dvd hr hd]
            exact Nat.mul_le_mul_left _ (Nat.totient_le v)
      · rw [Nat.totient_mul_of_prime_of_not_dvd hr hd]
        exact Nat.mul_le_mul_left _ (Nat.totient_le v)
    have H := Nat.mul_le_mul_left r haux
    have h1 := hr.pos
    zify [h1] at H ⊢
    nlinarith
  · rw [Nat.totient_mul_of_prime_of_not_dvd hr h]
    have H := Nat.mul_le_mul_left (r-1) (Nat.totient_le u)
    have h1 := hr.pos
    zify [h1] at H ⊢
    nlinarith

theorem four_odd_core {u : ℕ} (hu : Odd u) (hl : u.primeFactorsList.length=4) :
    81≤u ∧ u^3 ≤ (u-u.totient)^4 := by
  have hu0 : u≠0 := by have := Nat.odd_iff.mp hu; omega
  have hlist : ∃ a b c d, u.primeFactorsList=[a,b,c,d] := by
    cases he : u.primeFactorsList with
    | nil => simp [he] at hl
    | cons a l =>
      rcases l with _ | ⟨b,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨c,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨d,l⟩
      · simp [he] at hl
      rcases l with _ | ⟨e,l⟩
      · exact ⟨a,b,c,d,rfl⟩
      · simp [he] at hl
  obtain ⟨a,b,c,d,he⟩ := hlist
  have ha := Nat.prime_of_mem_primeFactorsList (n := u) (p := a) (by simp [he])
  have hsort := (Nat.primeFactorsList_sorted u).pairwise
  simp only [he,List.pairwise_cons,List.mem_cons,List.not_mem_nil,or_false] at hsort
  have hab := hsort.1 b (Or.inl rfl)
  have hac := hsort.1 c (Or.inr (Or.inl rfl))
  have had := hsort.1 d (Or.inr (Or.inr rfl))
  have hu' : u=a*(b*c*d) := by simpa [he,mul_assoc] using (Nat.prod_primeFactorsList hu0).symm
  have hao : Odd a := (Nat.odd_mul.mp (hu' ▸ hu)).1
  have ha3 : 3≤a := by have := ha.two_le; have := Nat.odd_iff.mp hao; omega
  have hprod : a^3≤b*c*d := by
    simpa only [pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul hab hac) had
  have hlow := Nat.mul_le_mul ha3 (show 27≤b*c*d from (Nat.pow_le_pow_left ha3 3).trans hprod)
  have hdef := phi_lower_defect (u:=b*c*d) ha
  rw [←hu'] at hdef
  have hdef' : b*c*d ≤ u-u.totient := by omega
  refine ⟨by omega,?_⟩
  conv_lhs => rw [hu',mul_pow]
  exact (Nat.mul_le_mul_right _ hprod).trans ((by ring : (b*c*d)*(b*c*d)^3=(b*c*d)^4) ▸
    Nat.pow_le_pow_left hdef' 4)

theorem no_two_times_prime_square_five {p m : ℕ} (hp : p.Prime) (hop : Odd p)
    (hm : m.primeFactorsList.length=5) (hg : 2*p^2+12=m ∨ m+12=2*p^2)
    (hφ : (2*p^2).totient+m=m.totient+2*p^2) : False := by
  have hme : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨u,hu⟩ := hme
  have hmu : m=2*u := by omega
  have hp2odd := hop.pow (n:=2)
  have huo : Odd u := by
    apply Nat.odd_iff.mpr
    have hpmod := Nat.odd_iff.mp hp2odd
    omega
  have hu0 : u≠0 := by have := Nat.odd_iff.mp huo; omega
  have hl : u.primeFactorsList.length=4 := by
    rw [hmu,len_mul (by decide) hu0,Nat.primeFactorsList_two,List.length_singleton] at hm
    omega
  obtain ⟨hlarge,hpow⟩ := four_odd_core huo hl
  rw [hmu,Nat.totient_two_mul_of_odd hp2odd,Nat.totient_two_mul_of_odd huo,
    show (p^2).totient=p*(p-1) by simpa using Nat.totient_prime_pow_succ hp 1] at hφ
  have hp1 := hp.pos
  have hP : 9≤p := by
    by_contra! h
    interval_cases p <;> norm_num at hφ hg hp <;> omega
  have hdef : u-u.totient≤p+6 := by
    have eq : p*(p-1)+p=p^2 := by zify [hp1]; ring
    omega
  have hu' : (p-1)^2≤u := by
    have he : (p-1)^2+2*p=p^2+1 := by zify [hp1]; ring
    omega
  have hp' : p+6≤2*(p-1) := by omega
  have hi : (p+6)^4≤(2*(p-1))^4 := Nat.pow_le_pow_left hp' 4
  have hj : (2*(p-1))^4<((p-1)^2)^3 := by
    have ha : 16<(p-1)^2 := by
      have H := Nat.pow_le_pow_left (show 8≤p-1 by omega) 2
      omega
    have H := Nat.mul_lt_mul_of_pos_right ha
      (show 0<(p-1)^4 from Nat.pow_pos (show 0<p-1 by omega))
    calc
      (2*(p-1))^4 = 16*(p-1)^4 := by ring
      _ < (p-1)^2*(p-1)^4 := H
      _ = ((p-1)^2)^3 := by ring
  exact (not_lt_of_ge (Nat.le_trans hpow (Nat.pow_le_pow_left hdef 4)))
    (hi.trans_lt (hj.trans_le (Nat.pow_le_pow_left hu' 3)))

private theorem sigma_four_times_prime {q : ℕ} (hq : q.Prime) (ho : Odd q) :
    σ 1 (4*q)=7*(q+1) := by
  have hc := (ho.coprime_two_left).pow_left 2
  rw [show (4:ℕ)=2^2 by decide,isMultiplicative_sigma.map_mul_of_coprime hc]
  rw [show σ 1 (2^2)=7 by decide]
  have hs : σ 1 q=q+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hq
  rw [hs]

theorem no_four_times_prime_five {q m : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : m.primeFactorsList.length=5) (hg : 4*q+12=m ∨ m+12=4*q)
    (hφ : (4*q).totient+m=m.totient+4*q) (hσ : σ 1 (4*q)+m=σ 1 m+4*q) : False := by
  have hm0 : m≠0 := by rintro rfl; simp at hm
  obtain ⟨k,u,hu,hmu⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  have hu0 : u≠0 := by have := Nat.odd_iff.mp hu; omega
  have hl : k+u.primeFactorsList.length=5 := by
    rw [hmu,len_mul (pow_ne_zero _ (by decide)) hu0,Nat.prime_two.primeFactorsList_pow,
      List.length_replicate] at hm
    exact hm
  have hqmod := Nat.odd_iff.mp ho
  have humod := Nat.odd_iff.mp hu
  have hk : 3≤k := by
    by_contra! h
    interval_cases k <;> norm_num at hmu <;> omega
  have hq2 := hq.two_le
  have hφq : (4*q).totient=2*(q-1) := by
    rw [show (4:ℕ)=2^2 by decide,Nat.totient_mul (ho.coprime_two_left.pow_left 2),
      Nat.totient_prime hq,show (2^2:ℕ).totient=2 by decide]
  rw [hφq] at hφ
  rw [sigma_four_times_prime hq ho] at hσ
  have hlow : m+12=4*q := by
    have hm2 : ∃ v, m=2*v := ⟨m/2,by omega⟩
    obtain ⟨v,hv⟩ := hm2
    have hbound := phi_lower_defect (u:=v) Nat.prime_two
    rw [←hv] at hbound
    omega
  have hFm (j : ℕ) (hj : 0<j) :
      (2^j*u).totient=2^(j-1)*u.totient := by
    rw [Nat.totient_mul (hu.coprime_two_left.pow_left j),Nat.totient_prime_pow Nat.prime_two hj]
    norm_num
  rcases (show k=3 ∨ k=4 ∨ k=5 by omega) with rfl|rfl|rfl
  · have h := hFm 3 (by decide)
    norm_num at h hmu
    rw [hmu,h] at hφ
    have hu1 : 1<u := by by_contra! hh; interval_cases u <;> simp at hl
    have hφeven := Nat.even_iff.mp (Nat.totient_even (show 2<u by omega))
    omega
  · have h := hFm 4 (by decide)
    norm_num at h hmu
    rw [hmu,h] at hφ
    have hlu : u.primeFactorsList.length=1 := by omega
    have hup : u.Prime := by
      obtain ⟨r,hr⟩ : ∃ r, u.primeFactorsList=[r] := by
        cases he : u.primeFactorsList with
        | nil => simp [he] at hlu
        | cons r l =>
          obtain rfl : l=[] := List.length_eq_zero_iff.mp (by simpa [he] using hlu)
          exact ⟨r,rfl⟩
      have hp := Nat.prime_of_mem_primeFactorsList (n:=u) (p:=r) (by simp [hr])
      have he : u=r := by simpa [hr] using (Nat.prod_primeFactorsList hu0).symm
      exact he ▸ hp
    have hs : σ 1 m=31*(u+1) := by
      rw [hmu,show (16:ℕ)=2^4 by decide,
        isMultiplicative_sigma.map_mul_of_coprime (hu.coprime_two_left.pow_left 4)]
      rw [show σ 1 (2^4)=31 by decide]
      have he : σ 1 u=u+1 := by simpa using sigma_one_apply_prime_pow (i:=1) hup
      rw [he]
    omega
  · have hh : u.primeFactorsList=[] := List.length_eq_zero_iff.mp (by omega)
    have he : u=1 := by simpa [hh] using (Nat.prod_primeFactorsList hu0).symm
    subst u
    have h : m=32 := by simpa using hmu
    subst m
    norm_num at hg hσ hφ
    have hs : σ 1 (32:ℕ)=63 := by decide
    omega

private theorem three_shape {n : ℕ} (hn : n.primeFactorsList.length=3) :
    Squarefree n ∨ (∃ p : ℕ, p.Prime ∧ n=p^3) ∨
      (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧ n=p^2*q) := by
  have hn0 : n≠0 := by rintro rfl; simp at hn
  obtain ⟨a,b,c,hl⟩ : ∃ a b c, n.primeFactorsList=[a,b,c] := by
    cases he : n.primeFactorsList with
    | nil => simp [he] at hn
    | cons a l =>
      rcases l with _ | ⟨b,l⟩
      · simp [he] at hn
      rcases l with _ | ⟨c,l⟩
      · simp [he] at hn
      obtain rfl : l=[] := List.length_eq_zero_iff.mp (by simpa [he] using hn)
      exact ⟨a,b,c,rfl⟩
  have ha := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=a) (by simp [hl])
  have hb := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=b) (by simp [hl])
  have hc := Nat.prime_of_mem_primeFactorsList (n:=n) (p:=c) (by simp [hl])
  have he : n=a*b*c := by simpa [hl,mul_assoc] using (Nat.prod_primeFactorsList hn0).symm
  by_cases hab : a=b
  · subst b
    by_cases hac : a=c
    · subst c
      exact Or.inr (Or.inl ⟨a,ha,by rw [he]; ring⟩)
    · exact Or.inr (Or.inr ⟨a,c,ha,hc,hac,by rw [he]; ring⟩)
  · by_cases hac : a=c
    · subst c
      exact Or.inr (Or.inr ⟨a,b,ha,hb,hab,by rw [he]; ring⟩)
    · by_cases hbc : b=c
      · subst c
        exact Or.inr (Or.inr ⟨b,a,hb,ha,Ne.symm hab,by rw [he]; ring⟩)
      · left
        rw [he]
        exact Nat.squarefree_mul_iff.mpr
          ⟨((Nat.coprime_primes ha hc).mpr hac).mul_left ((Nat.coprime_primes hb hc).mpr hbc),
            Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes ha hb).mpr hab,ha.squarefree,hb.squarefree⟩,
            hc.squarefree⟩

/-- All even three-versus-five pairs are excluded under the two jump conditions. -/
theorem no_even_three_five_pair {n m : ℕ} (hn : n.primeFactorsList.length=3)
    (hm : m.primeFactorsList.length=5) (he : Even n) (hg : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) : False := by
  rcases three_shape hn with hs | ⟨p,hp,rfl⟩ | ⟨p,q,hp,hq,hpq,rfl⟩
  · exact A056777EvenSquarefreeThreeFive.no_even_squarefree_three_five_pair hn hm hs he hg hφ hσ
  · exact A056777CubeFive.no_cube_five_pair hp hm hg hφ hσ
  · rcases hp.eq_two_or_odd with rfl|hpo
    · have hqo := hq.eq_two_or_odd.resolve_left (Ne.symm hpq)
      exact no_four_times_prime_five hq (Nat.odd_iff.mpr hqo) hm hg hφ hσ
    · rcases hq.eq_two_or_odd with rfl|hqo
      · rw [mul_comm (p^2) 2] at hg hφ
        exact no_two_times_prime_square_five hp (Nat.odd_iff.mpr hpo) hm hg hφ
      · exact (Nat.not_even_iff_odd.mpr (((Nat.odd_iff.mpr hpo).pow (n:=2)).mul (Nat.odd_iff.mpr hqo))) he

/-- A three-versus-five pair reduces to two odd configurations. -/
theorem remaining_three_five_pair {n m : ℕ} (hn : n.primeFactorsList.length=3)
    (hm : m.primeFactorsList.length=5) (hg : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m=σ 1 m+n) :
    (m+12=n ∧ Squarefree n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p≠q ∧
      p%4=3 ∧ q%8=3 ∧ 11≤q ∧ 2*q<p ∧ p%3≠q%3 ∧ p^2<q^3 ∧
      (p%5=2 ∨ p%5=3) ∧ q%5=2 ∧ m=p^4*q) ∨
    (Odd m ∧ ¬Squarefree m ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧
      Odd p ∧ Odd q ∧ p≠q ∧ n=p^2*q) := by
  have ho : Odd n := Nat.not_even_iff_odd.mp (fun he => no_even_three_five_pair hn hm he hg hφ hσ)
  rcases three_shape hn with hs | ⟨p,hp,rfl⟩ | ⟨p,q,hp,hq,hpq,hshape⟩
  · obtain ⟨h,hr⟩ := A056777OddSquarefreeThreeFive.odd_squarefree_three_five_orientation_mod_five
      hn hm hs ho hg hφ hσ
    exact Or.inl ⟨h,hs,hr⟩
  · exact (A056777CubeFive.no_cube_five_pair hp hm hg hφ hσ).elim
  · right
    have hmO : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
    have hmN : ¬Squarefree m := fun hmS =>
      A056777ThreeSquarefreeFive.no_three_squarefree_five_pair hn hm hmS hg hφ hσ
    have hodd := Nat.odd_mul.mp (hshape ▸ ho)
    have hpo := (odd_pow_iff (by decide : 2≠0)).mp hodd.1
    exact ⟨hmO,hmN,p,q,hp,hq,hpo,hodd.2,hpq,hshape⟩

end A056777EvenRepeatedThreeFive

#print axioms A056777EvenRepeatedThreeFive.remaining_three_five_pair
