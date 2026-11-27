import A056777ThreeSquarefreeFive

open scoped ArithmeticFunction.sigma

namespace A056777CubeFive

/-- A prime cube has no five-factor partner at distance twelve with the same totient and sigma jumps. -/
theorem no_cube_five_pair {p m : ℕ} (hp : p.Prime) (hm : m.primeFactorsList.length = 5)
    (hgap : p^3+12=m ∨ m+12=p^3)
    (hφ : (p^3).totient+m=m.totient+p^3) (hσ : σ 1 (p^3)+m=σ 1 m+p^3) :
    False := by
  by_cases hs : Squarefree m
  · have hlength : (p^3).primeFactorsList.length=3 := by
      rw [hp.primeFactorsList_pow]
      simp
    exact A056777ThreeSquarefreeFive.no_three_squarefree_five_pair hlength hm hs hgap hφ hσ
  · rw [Nat.squarefree_iff_prime_squarefree] at hs
    push Not at hs
    obtain ⟨r,hr,hrs⟩ := hs
    have hrs : r^2∣m := by simpa only [pow_two] using hrs
    have hrm : r∣m := (dvd_pow_self r (by decide : 2≠0)).trans hrs
    have hrt : r∣m.totient := by
      apply dvd_trans _ (Nat.totient_dvd_of_dvd hrs)
      rw [show (r^2).totient=r*(r-1) by simpa using Nat.totient_prime_pow_succ hr 1]
      exact dvd_mul_right _ _
    have hdef : (p^3).totient+p^2=p^3 := by
      rw [show (p^3).totient=p^2*(p-1) from Nat.totient_prime_pow_succ hp 2]
      have hp1 := hp.pos
      zify [hp1]
      ring
    have hh : m.totient+p^2=m := by omega
    have hrp : r=p := by
      have H : r∣m.totient+p^2 := by rwa [hh]
      have hdiv : r∣p^2 := (Nat.dvd_add_iff_right hrt).mpr H
      have hpr := hr.dvd_of_dvd_pow hdiv
      exact (Nat.dvd_prime hp).mp hpr |>.resolve_left hr.ne_one
    subst r
    have h12 : p∣12 := by
      have hcube := dvd_pow_self p (by decide : 3≠0)
      rcases hgap with h|h
      · have H : p∣p^3+12 := by rwa [h]
        exact (Nat.dvd_add_iff_right hcube).mpr H
      · have H : p∣m+12 := by rwa [h]
        exact (Nat.dvd_add_iff_right hrm).mpr H
    have hsmall : p=2 ∨ p=3 := by
      have he : p∣2^2*3 := h12
      rcases hp.dvd_mul.mp he with h|h
      · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h) |>.resolve_left hp.ne_one)
      · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one)
    have len_mul {a b : ℕ} (ha : a≠0) (hb : b≠0) :
        (a*b).primeFactorsList.length=a.primeFactorsList.length+b.primeFactorsList.length := by
      simpa using (Nat.perm_primeFactorsList_mul ha hb).length_eq
    rcases hsmall with rfl|rfl
    · have he : m=20 := by norm_num at hgap; omega
      subst m
      change (2^2*5).primeFactorsList.length=5 at hm
      rw [len_mul (by decide) (by decide),Nat.prime_two.primeFactorsList_pow,
        Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hm
      simp at hm
    · have he : m=39 ∨ m=15 := by norm_num at hgap; omega
      rcases he with rfl|rfl
      · change (3*13).primeFactorsList.length=5 at hm
        rw [len_mul (by decide) (by decide),Nat.primeFactorsList_prime Nat.prime_three,
          Nat.primeFactorsList_prime (by decide : Nat.Prime 13)] at hm
        simp at hm
      · change (3*5).primeFactorsList.length=5 at hm
        rw [len_mul (by decide) (by decide),Nat.primeFactorsList_prime Nat.prime_three,
          Nat.primeFactorsList_prime (by decide : Nat.Prime 5)] at hm
        simp at hm

end A056777CubeFive

#print axioms A056777CubeFive.no_cube_five_pair
