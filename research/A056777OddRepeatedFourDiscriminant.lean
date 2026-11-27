import A056777OddRepeatedFour

open scoped ArithmeticFunction.sigma
open Nat

namespace A056777OddRepeatedFourDiscriminant

private def sumDenominator (p r : ℤ) : ℤ := r*(p*r+2*p-r^2+r)

private def sumNumerator (p r D : ℤ) : ℤ :=
  D-p^3+p^2*r+p^2-2*p*r^3-p*r^2+2*p*r-r^3+r^2

private def discriminantNumerator (p r D : ℤ) : ℤ :=
  let C := sumDenominator p r
  let N := sumNumerator p r D
  (r^2-p^2)*N^2-4*(p^2*((2*r+1)*N+(2*r^2-2*p)*C)+D*C)*C

private theorem negative_discriminant_positive (P J : ℤ)
    (hP : 0 ≤ P) (hJ : 0 ≤ J) :
    discriminantNumerator (P+7) (P+7+(J+6)) (12) < 0 := by
  let c : ℤ := (11111035680 + P * (9560359728 + P * (3477284496 + P * (702370608 + P * (86539872 + P * (6680400 + P * (316176 + P * (8400 + P * (96))))))))) + J * ((23791396824 + P * (20204722512 + P * (7431611784 + P * (1560716088 + P * (207133352 + P * (18092584 + P * (1044536 + P * (38600 + P * (832 + P * (8)))))))))) + J * ((10349002332 + P * (8075711568 + P * (2690368956 + P * (501632872 + P * (57465032 + P * (4155616 + P * (185836 + P * (4712 + P * (52))))))))) + J * ((2110708104 + P * (1488566160 + P * (438170504 + P * (70027952 + P * (6586632 + P * (365840 + P * (11144 + P * (144)))))))) + J * ((244697100 + P * (153708960 + P * (39033836 + P * (5146108 + P * (372972 + P * (14144 + P * (220))))))) + J * ((17138866 + P * (9427206 + P * (2001736 + P * (205584 + P * (10260 + P * (200)))))) + J * ((720739 + P * (339604 + P * (57532 + P * (4148 + P * (108))))) + J * ((16796 + P * (6578 + P * (820 + P * (32)))) + J * ((167 + P * (52 + P * (4)))))))))))
  have hc : 0 < c := by dsimp [c]; positivity
  have he : -discriminantNumerator (P+7) (P+7+(J+6)) (12) = c := by
    dsimp [discriminantNumerator, sumNumerator, sumDenominator, c]
    ring
  omega

private theorem negative_discriminant_negative (P J : ℤ)
    (hP : 0 ≤ P) (hJ : 0 ≤ J) :
    discriminantNumerator (P+7) (P+7+(J+6)) (-12) < 0 := by
  let c : ℤ := (10960405920 + P * (9501175152 + P * (3467757456 + P * (701582640 + P * (86506464 + P * (6679824 + P * (316176 + P * (8400 + P * (96))))))))) + J * ((23711473656 + P * (20179880784 + P * (7428687432 + P * (1560560568 + P * (207130184 + P * (18092584 + P * (1044536 + P * (38600 + P * (832 + P * (8)))))))))) + J * ((10329260508 + P * (8070685680 + P * (2689913724 + P * (501616072 + P * (57464840 + P * (4155616 + P * (185836 + P * (4712 + P * (52))))))))) + J * ((2108109672 + P * (1488047376 + P * (438137288 + P * (70027280 + P * (6586632 + P * (365840 + P * (11144 + P * (144)))))))) + J * ((244512444 + P * (153683328 + P * (39032972 + P * (5146108 + P * (372972 + P * (14144 + P * (220))))))) + J * ((17132194 + P * (9426726 + P * (2001736 + P * (205584 + P * (10260 + P * (200)))))) + J * ((720643 + P * (339604 + P * (57532 + P * (4148 + P * (108))))) + J * ((16796 + P * (6578 + P * (820 + P * (32)))) + J * ((167 + P * (52 + P * (4)))))))))))
  have hc : 0 < c := by dsimp [c]; positivity
  have he : -discriminantNumerator (P+7) (P+7+(J+6)) (-12) = c := by
    dsimp [discriminantNumerator, sumNumerator, sumDenominator, c]
    ring
  omega

private theorem negative_discriminant (p r D : ℤ) (hp : 7 ≤ p) (hr : p+6 ≤ r)
    (hD : D=12 ∨ D=-12) : discriminantNumerator p r D < 0 := by
  let P := p-7
  let J := r-p-6
  have hP : 0 ≤ P := by dsimp [P]; omega
  have hJ : 0 ≤ J := by dsimp [J]; omega
  have hp' : P+7=p := by dsimp [P]; omega
  have hr' : P+7+(J+6)=r := by dsimp [P,J]; omega
  rcases hD with rfl | rfl
  · have h := negative_discriminant_positive P J hP hJ
    rw [hr',hp'] at h
    exact h
  · have h := negative_discriminant_negative P J hP hJ
    rw [hr',hp'] at h
    exact h

private theorem nonnegative_discriminant (p r A B D : ℤ) (hpr : 0 < r^2-p^2)
    (hA : sumDenominator p r * A = sumNumerator p r D)
    (hB : (r^2-p^2)*B=p^2*((2*r+1)*A+2*r^2-2*p)+D)
    (hdisc : 4*B ≤ A^2) :
    0 ≤ discriminantNumerator p r D := by
  have he : discriminantNumerator p r D =
      (r^2-p^2)*(sumDenominator p r)^2*(A^2-4*B) := by
    unfold discriminantNumerator
    dsimp only
    rw [← hA]
    linear_combination 4*(sumDenominator p r)^2*hB
  rw [he]
  exact mul_nonneg (mul_nonneg hpr.le (sq_nonneg _)) (sub_nonneg.mpr hdisc)

private theorem prime_of_dvd_four_times_prime {r a : ℕ} (hr : r.Prime) (ha : a.Prime)
    (hbig : 2 < r) (h : r ∣ 4*a) : r=a := by
  rcases hr.dvd_mul.mp h with h₄ | hₐ
  · have hh : r ∣ 2^2 := h₄
    have h₂ := hr.dvd_of_dvd_pow hh
    rcases (Nat.dvd_prime Nat.prime_two).mp h₂ with h | h <;> omega
  · rcases (Nat.dvd_prime ha).mp hₐ with h | h <;> omega

/-- The last odd three-versus-four shape cannot satisfy both jump conditions. -/
theorem no_odd_square_prime_square_two_primes_pair {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hop : Odd p) (hoq : Odd q) (hor : Odd r) (hos : Odd s) (hot : Odd t)
    (hgap : p^2*q+12 = r^2*s*t ∨ r^2*s*t+12 = p^2*q)
    (hφ : (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q)
    (hσ : σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q) : False := by
  obtain ⟨hsep,hp4,_,_,_⟩ :=
    A056777OddRepeatedFour.odd_square_prime_square_two_primes_constraints hp hq hr hs ht
      hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  have hp7 := A056777OddRepeatedFour.odd_square_prime_square_two_primes_seven_le hp hq hr hs ht
    hpq hrs hrt hst hop hoq hor hos hot hgap hφ hσ
  let D : ℤ := (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q
  have hD : D=12 ∨ D=-12 := by
    zify at hgap
    dsimp [D]
    simp only [mul_assoc] at hgap ⊢
    omega
  have h : (r:ℤ)^2*((s:ℤ)*t)-(p:ℤ)^2*q=D ∧
      (p^2*q).totient+r^2*s*t = (r^2*s*t).totient+p^2*q ∧
      σ 1 (p^2*q)+r^2*s*t = σ 1 (r^2*s*t)+p^2*q := ⟨rfl,hφ,hσ⟩
  obtain ⟨_, hA, hB⟩ :=
    (A056777OddRepeatedFour.moment_criterion D hp hq hr hs ht hpq hrs hrt hst).mp h
  have hA' : sumDenominator p r *((s:ℤ)+t) = sumNumerator p r D := hA
  have hpr : 0 < (r:ℤ)^2-(p:ℤ)^2 := by
    have h₁ : 0 < (r:ℤ)-(p:ℤ) := by
      have h' : (p:ℤ) < r := by exact_mod_cast (show p < r by omega)
      omega
    have h₂ : 0 < (r:ℤ)+(p:ℤ) := by
      have := hr.pos
      positivity
    nlinarith only [mul_pos h₁ h₂]
  have hdisc : 4*((s:ℤ)*t) ≤ ((s:ℤ)+t)^2 := by nlinarith only [sq_nonneg ((s:ℤ)-t)]
  have hNonneg := nonnegative_discriminant p r ((s:ℤ)+t) ((s:ℤ)*t) D hpr hA' hB hdisc
  have hclose : r < p+6 := by
    by_contra! hh
    exact (not_lt_of_ge hNonneg) (negative_discriminant p r D
      (by exact_mod_cast hp7) (by exact_mod_cast hh) hD)
  have hop2 := Nat.odd_iff.mp hop
  have hor2 := Nat.odd_iff.mp hor
  have hrp : r = p+4 := by omega
  have hdist : (r:ℤ)-(p:ℤ)=4 := by
    have h' : (r:ℤ)=(p:ℤ)+4 := by exact_mod_cast hrp
    omega
  have hdvd := A056777OddRepeatedFour.repeated_prime_distance_sieve D
    (A056777OddRepeatedFour.prime_divisor_sieve D hp hq hr hs ht hpq hrs hrt hst h)
  rw [hdist] at hdvd
  rcases hD with hD | hD
  · rw [hD] at hdvd hA
    have hd : r ∣ 4*23 := by exact_mod_cast hdvd
    have hr23 := prime_of_dvd_four_times_prime hr (by decide : Nat.Prime 23) (by omega) hd
    have hp19 : p=19 := by omega
    rw [hr23,hp19] at hA
    norm_num at hA
    omega
  · rw [hD] at hdvd
    norm_num at hdvd
    have hd : r ∣ 4*17 := by exact_mod_cast hdvd
    have hr17 := prime_of_dvd_four_times_prime hr (by decide : Nat.Prime 17) (by omega) hd
    omega

end A056777OddRepeatedFourDiscriminant

#print axioms A056777OddRepeatedFourDiscriminant.no_odd_square_prime_square_two_primes_pair
