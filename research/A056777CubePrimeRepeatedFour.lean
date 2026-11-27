import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubePrimeRepeatedFour

private def momentDeterminant (p r : ℤ) : ℤ :=
  r*(p^3*r+2*p^3-2*p^2*r^2-p^2*r+p*r^3-p*r^2+r^3-r^2)

private def baseExcess (p r : ℤ) : ℤ := p+2*p^2-2*r^2

private def baseDeficit (p r : ℤ) : ℤ := p^2*(p-1)+r*(r-1)

private def sumNumerator (p r D : ℤ) : ℤ :=
  p^2*r*(p-r)*baseExcess p r-(p^3-p*r^2-r^2)*baseDeficit p r+(p^2-p*r-r)*D

private def productNumerator (p r D : ℤ) : ℤ :=
  -p^3*r*(r-1)*baseExcess p r+
  p^3*(2*r+1)*baseDeficit p r+(-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*D

private def discriminantNumerator (p r D : ℤ) : ℤ :=
  (sumNumerator p r D)^2-4*productNumerator p r D*momentDeterminant p r

private theorem moment_equations (p q r A B D : ℤ)
    (hK : (p+1)*(q+1)+2*p^2-(B+(2*r+1)*A+2*r^2+1)=0)
    (hF : p^2*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^3*q-D=0) :
    momentDeterminant p r * A = sumNumerator p r D ∧
      momentDeterminant p r * B = productNumerator p r D := by
  constructor
  · dsimp [momentDeterminant,sumNumerator,baseExcess,baseDeficit]
    linear_combination (-p^2*r*(p-r))*hK+(p^3-p*r^2-r^2)*hF+(p^2-p*r-r)*hG
  · dsimp [momentDeterminant,productNumerator,baseExcess,baseDeficit]
    linear_combination (p^3*r*(r-1))*hK+(-p^3*(2*r+1))*hF+
      (-2*p^2*r-p^2+p*r^2-p*r+r^2-r)*hG

/- The following five certificates are Horner decompositions after shifting the
two repeated bases into the appropriate nonnegative quadrant. The ring tactic
verifies each displayed polynomial identity over the integers. -/
private theorem negative_disc_positive_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    discriminantNumerator (U+3) (U+3+V) (12) < 0 := by
  let c0 : ℤ := 741312+U*(3034368+U*(5533776+U*(5968800+U*(4246287+U*(2097558+U*(735569+U*(183388+U*(31889+U*(3686+U*(255+U*(8)))))))))))
  let c1 : ℤ := 644544+U*(2369664+U*(3961800+U*(3934572+U*(2556642+U*(1132638+U*(346120+U*(72040+U*(9778+U*(782+U*(28))))))))))
  let c2 : ℤ := 597744+U*(2113488+U*(3307176+U*(3006378+U*(1751721+U*(680794+U*(177738+U*(30506+U*(3241+U*(186+U*(4))))))))))
  let c3 : ℤ := 472464+U*(1543200+U*(2191140+U*(1775044+U*(903130+U*(298728+U*(64052+U*(8544+U*(638+U*(20)))))))))
  let c4 : ℤ := 322764+U*(904620+U*(1104219+U*(760428+U*(321462+U*(85138+U*(13758+U*(1236+U*(47))))))))
  let c5 : ℤ := 163944+U*(390672+U*(398602+U*(223550+U*(74040+U*(14440+U*(1532+U*(68)))))))
  let c6 : ℤ := 47684+U*(96252+U*(80257+U*(35180+U*(8528+U*(1082+U*(56))))))
  let c7 : ℤ := 6920+U*(11600+U*(7622+U*(2456+U*(388+U*(24)))))
  let c8 : ℤ := 380+U*(508+U*(247+U*(52+U*(4))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    positivity
  have he : -(discriminantNumerator (U+3) (U+3+V) (12)) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [momentDeterminant, sumNumerator, productNumerator, discriminantNumerator,
      baseExcess, baseDeficit, c0, c1, c2, c3, c4, c5, c6, c7, c8]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_sum_positive_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    sumNumerator (U+3+1+V) (U+3) (12) < 0 := by
  let c0 : ℤ := 150+U*(381+U*(289+U*(99+U*(16+U*(1)))))
  let c1 : ℤ := 694+U*(1289+U*(830+U*(250+U*(36+U*(2)))))
  let c2 : ℤ := 599+U*(745+U*(340+U*(68+U*(5))))
  let c3 : ℤ := 325+U*(249+U*(66+U*(6)))
  let c4 : ℤ := 106+U*(50+U*(6))
  let c5 : ℤ := 17+U*(4)
  let c6 : ℤ := 1
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    positivity
  have he : -(sumNumerator (U+3+1+V) (U+3) (12)) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [momentDeterminant, sumNumerator, productNumerator, discriminantNumerator,
      baseExcess, baseDeficit, c0, c1, c2, c3, c4, c5, c6]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_disc_negative_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    discriminantNumerator (U+3) (U+3+V) (-12) < 0 := by
  let c0 : ℤ := 912384+U*(3449088+U*(5962752+U*(6214464+U*(4330479+U*(2114838+U*(737537+U*(183484+U*(31889+U*(3686+U*(255+U*(8)))))))))))
  let c1 : ℤ := 514944+U*(2144160+U*(3800664+U*(3874476+U*(2544450+U*(1131390+U*(346072+U*(72040+U*(9778+U*(782+U*(28))))))))))
  let c2 : ℤ := 532944+U*(2009376+U*(3240792+U*(2985498+U*(1748505+U*(680602+U*(177738+U*(30506+U*(3241+U*(186+U*(4))))))))))
  let c3 : ℤ := 433008+U*(1482096+U*(2155716+U*(1765540+U*(901978+U*(298680+U*(64052+U*(8544+U*(638+U*(20)))))))))
  let c4 : ℤ := 276204+U*(849660+U*(1080699+U*(756108+U*(321174+U*(85138+U*(13758+U*(1236+U*(47))))))))
  let c5 : ℤ := 148968+U*(378288+U*(395290+U*(223262+U*(74040+U*(14440+U*(1532+U*(68)))))))
  let c6 : ℤ := 46148+U*(95484+U*(80161+U*(35180+U*(8528+U*(1082+U*(56))))))
  let c7 : ℤ := 6920+U*(11600+U*(7622+U*(2456+U*(388+U*(24)))))
  let c8 : ℤ := 380+U*(508+U*(247+U*(52+U*(4))))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6, c7, c8]
    positivity
  have he : -(discriminantNumerator (U+3) (U+3+V) (-12)) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6+V*(c7+V*(c8)))))))) := by
    dsimp [momentDeterminant, sumNumerator, productNumerator, discriminantNumerator,
      baseExcess, baseDeficit, c0, c1, c2, c3, c4, c5, c6, c7, c8]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem negative_sum_negative_gap (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    sumNumerator (U+3+1+V) (U+3) (-12) < 0 := by
  let c0 : ℤ := 174+U*(381+U*(289+U*(99+U*(16+U*(1)))))
  let c1 : ℤ := 814+U*(1313+U*(830+U*(250+U*(36+U*(2)))))
  let c2 : ℤ := 623+U*(745+U*(340+U*(68+U*(5))))
  let c3 : ℤ := 325+U*(249+U*(66+U*(6)))
  let c4 : ℤ := 106+U*(50+U*(6))
  let c5 : ℤ := 17+U*(4)
  let c6 : ℤ := 1
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [c0, c1, c2, c3, c4, c5, c6]
    positivity
  have he : -(sumNumerator (U+3+1+V) (U+3) (-12)) = c0+V*(c1+V*(c2+V*(c3+V*(c4+V*(c5+V*(c6)))))) := by
    dsimp [momentDeterminant, sumNumerator, productNumerator, discriminantNumerator,
      baseExcess, baseDeficit, c0, c1, c2, c3, c4, c5, c6]
    ring
  rw [← he] at hpos
  exact neg_pos.mp hpos

private theorem positive_determinant (U V : ℤ) (hU : 0 ≤ U) (hV : 0 ≤ V) :
    0 < momentDeterminant (U+3+1+V) (U+3) := by
  let c0 : ℤ := 222+U*(227+U*(87+U*(15+U*(1))))
  let c1 : ℤ := 270+U*(219+U*(58+U*(5)))
  let c2 : ℤ := 117+U*(81+U*(17+U*(1)))
  let c3 : ℤ := 15+U*(8+U*(1))
  have hpos : 0 < c0+V*(c1+V*(c2+V*(c3))) := by
    dsimp [c0, c1, c2, c3]
    positivity
  have he : momentDeterminant (U+3+1+V) (U+3) = c0+V*(c1+V*(c2+V*(c3))) := by
    dsimp [momentDeterminant, sumNumerator, productNumerator, discriminantNumerator,
      baseExcess, baseDeficit, c0, c1, c2, c3]
    ring
  rw [← he] at hpos
  exact hpos

private theorem impossible_moments (p q r A B D : ℤ)
    (hp : 3 ≤ p) (hr : 3 ≤ r) (hA : 0 ≤ A) (hdisc : 4*B ≤ A^2)
    (hD : D=12 ∨ D=-12)
    (hK : (p+1)*(q+1)+2*p^2-(B+(2*r+1)*A+2*r^2+1)=0)
    (hF : p^2*(p+q-1)-r*B-r*(r-1)*(A-1)=0)
    (hG : r^2*B-p^3*q-D=0) : False := by
  obtain ⟨hS,hP⟩ := moment_equations p q r A B D hK hF hG
  by_cases hpr : p ≤ r
  · let U := p-3
    let V := r-p
    have hU : 0 ≤ U := by dsimp [U]; omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hbase : U+3=p := by dsimp [U]; omega
    have hbase' : U+3+V=r := by dsimp [U,V]; omega
    have hneg : discriminantNumerator p r D < 0 := by
      rcases hD with rfl | rfl
      · have h := negative_disc_positive_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
      · have h := negative_disc_negative_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
    have hnneg : 0 ≤ discriminantNumerator p r D := by
      unfold discriminantNumerator
      rw [← hS,← hP]
      have he : (momentDeterminant p r*A)^2-4*(momentDeterminant p r*B)*momentDeterminant p r =
          (momentDeterminant p r)^2*(A^2-4*B) := by ring
      rw [he]
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hdisc)
    exact (not_lt_of_ge hnneg) hneg
  · let U := r-3
    let V := p-r-1
    have hU : 0 ≤ U := by dsimp [U]; omega
    have hV : 0 ≤ V := by dsimp [V]; omega
    have hbase : U+3=r := by dsimp [U]; omega
    have hbase' : U+3+1+V=p := by dsimp [U,V]; omega
    have hpos := positive_determinant U V hU hV
    rw [hbase',hbase] at hpos
    have hneg : sumNumerator p r D < 0 := by
      rcases hD with rfl | rfl
      · have h := negative_sum_positive_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
      · have h := negative_sum_negative_gap U V hU hV
        rw [hbase',hbase] at h
        exact h
    exact (not_lt_of_ge ((hS ▸ mul_nonneg hpos.le hA) : 0 ≤ sumNumerator p r D)) hneg

private theorem exclude_two_bases {q s t : ℕ} (hq : q.Prime) (hs : s.Prime) (ht : t.Prime)
    (hq2 : q ≠ 2) (hs2 : s ≠ 2) (ht2 : t ≠ 2) (hst : s ≠ t)
    (hgap : 2^3*q+12=2^2*s*t ∨ 2^2*s*t+12=2^3*q)
    (hφ : (2^3*q).totient+2^2*s*t = (2^2*s*t).totient+2^3*q) : False := by
  have hcq := ((Nat.coprime_primes Nat.prime_two hq).mpr hq2.symm).pow_left 3
  have hcs := ((Nat.coprime_primes Nat.prime_two hs).mpr hs2.symm).pow_left 2
  have hct := (((Nat.coprime_primes Nat.prime_two ht).mpr ht2.symm).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  rw [Nat.totient_mul hcq,Nat.totient_mul hct,Nat.totient_mul hcs,
    show ((2:ℕ)^3).totient=4 by decide,show ((2:ℕ)^2).totient=2 by decide,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at hφ
  have hq1 := hq.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  have hs3 : 3 ≤ s := by have := hs.two_le; omega
  have ht3 : 3 ≤ t := by have := ht.two_le; omega
  zify [hq1,hs1,ht1] at hφ hgap hs3 ht3
  norm_num at hφ hgap
  have he : (s:ℤ)+t ≤ 6 := by
    rcases hgap with h | h <;> nlinarith only [hφ,h]
  omega

/-- The last cube-times-prime versus four-factor shape is impossible.
Both orientations of the twelve-step are covered. -/
theorem no_cube_prime_square_two_primes_gap_twelve {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : p^3*q+12=r^2*s*t ∨ r^2*s*t+12=p^3*q)
    (hφ : (p^3*q).totient+r^2*s*t = (r^2*s*t).totient+p^3*q)
    (hσ : σ 1 (p^3*q)+r^2*s*t = σ 1 (r^2*s*t)+p^3*q) : False := by
  by_cases hp2 : p=2
  · subst p
    by_cases hr2 : r=2
    · subst r
      exact exclude_two_bases hq hs ht hpq.symm hrs.symm hrt.symm hst hgap hφ
    · have hd : 4 ∣ r^2*(s*t) := by
        rw [← mul_assoc]
        norm_num at hgap
        omega
      have hcop := (((Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)).pow_left 2).pow_right 2
      have hd' : 4 ∣ s*t := hcop.dvd_of_dvd_mul_left hd
      have hsfree : Squarefree (s*t) :=
        Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes hs ht).mpr hst,hs.squarefree,ht.squarefree⟩
      exact (Nat.squarefree_iff_prime_squarefree.mp hsfree 2 Nat.prime_two) hd'
  by_cases hr2 : r=2
  · subst r
    have hd : 4 ∣ p^3*q := by
      norm_num at hgap
      simp only [mul_assoc] at hgap
      omega
    have hcop := (((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)).pow_left 2).pow_right 3
    have hd' : 4 ∣ q := hcop.dvd_of_dvd_mul_left hd
    rcases (Nat.dvd_prime hq).mp hd' with h | h
    · omega
    · have hn : ¬ Nat.Prime 4 := by decide
      exact hn (h.symm ▸ hq)
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hr3 : 3 ≤ r := by have := hr.two_le; omega
  have hcp := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 3
  have hcrs := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 2
  have hcrt := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hSigma {a : ℕ} (ha : a.Prime) : σ 1 a = a+1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) ha
  have hSigma2 : σ 1 (r^2) = 1+r+r^2 := by
    simp only [sigma_one_apply_prime_pow hr,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hSigma3 : σ 1 (p^3) = 1+p+p^2+p^3 := by
    simp only [sigma_one_apply_prime_pow hp,Finset.sum_range_succ,Finset.sum_range_zero,
      pow_zero,pow_one,zero_add]
  have hPhi2 : (r^2).totient = r*(r-1) := by simpa using Nat.totient_prime_pow_succ hr 1
  have hPhi3 : (p^3).totient = p^2*(p-1) := Nat.totient_prime_pow_succ hp 2
  rw [Nat.totient_mul hcp,Nat.totient_mul hcrt,Nat.totient_mul hcrs,hPhi3,hPhi2,
    Nat.totient_prime hq,Nat.totient_prime hs,Nat.totient_prime ht] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hcp,isMultiplicative_sigma.map_mul_of_coprime hcrt,
    isMultiplicative_sigma.map_mul_of_coprime hcrs,hSigma3,hSigma2,hSigma hq,hSigma hs,hSigma ht] at hσ
  have hp1 := hp.pos
  have hq1 := hq.pos
  have hr1 := hr.pos
  have hs1 := hs.pos
  have ht1 := ht.pos
  zify [hp1,hq1,hr1,hs1,ht1] at hp3 hr3 hφ hσ hgap
  let D : ℤ := (r:ℤ)^2*s*t-(p:ℤ)^3*q
  have hD : D=12 ∨ D=-12 := by dsimp [D]; omega
  exact impossible_moments p q r (s+t) (s*t) D hp3 hr3 (by positivity)
    (by nlinarith only [sq_nonneg ((s:ℤ)-t)]) hD
    (by nlinarith only [hφ,hσ]) (by nlinarith only [hφ]) (by dsimp [D]; ring)

end A056777CubePrimeRepeatedFour

#print axioms A056777CubePrimeRepeatedFour.no_cube_prime_square_two_primes_gap_twelve
