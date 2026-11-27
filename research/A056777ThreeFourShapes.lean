import A056777MixedFourApplication
import A056777OddFour
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777ThreeFourShapes

private theorem length_mul_two_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (2*n).primeFactorsList.length = 1 + n.primeFactorsList.length := by
  have hh := (Nat.perm_primeFactorsList_mul (by decide : (2 : ℕ) ≠ 0) hn).length_eq
  rwa [Nat.primeFactorsList_two, List.length_append, List.length_singleton] at hh

private theorem excess_repeated {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s) :
    σ 1 (r^2*s) + (r^2*s).totient = 2*(r^2*s) + s + 2*r + 1 := by
  have hc := ((Nat.coprime_primes hr hs).mpr hne).pow_left 2
  have hσr : σ 1 (r^2) = 1+r+r^2 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hσs : σ 1 s = s+1 := by simpa using sigma_one_apply_prime_pow (i := 1) hs
  have hφr : (r^2).totient = r*(r-1) := by simpa using Nat.totient_prime_pow_succ hr 1
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, hσr, hσs,
    Nat.totient_mul hc, hφr, Nat.totient_prime hs]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  zify [hr₁,hs₁]
  ring

private theorem excess_cube {r : ℕ} (hr : r.Prime) :
    σ 1 (r^3) + (r^3).totient = 2*r^3+r+1 := by
  have hσ : σ 1 (r^3) = 1+r+r^2+r^3 := by
    simp only [sigma_one_apply_prime_pow hr, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  rw [hσ, show (r^3).totient = r^2*(r-1) from Nat.totient_prime_pow_succ hr 2]
  have hr₁ := hr.pos
  zify [hr₁]
  ring

private theorem totient_238 : (238 : ℕ).totient = 96 := by
  have h₂ : (2 : ℕ).Coprime 119 := by decide
  have h₇ : (7 : ℕ).Coprime 17 := by decide
  have hp₇ : Nat.Prime 7 := by decide
  have hp₁₇ : Nat.Prime 17 := by decide
  rw [show (238 : ℕ) = 2*119 by decide, Nat.totient_mul h₂, Nat.totient_prime Nat.prime_two,
    show (119 : ℕ) = 7*17 by decide, Nat.totient_mul h₇,
    Nat.totient_prime hp₇, Nat.totient_prime hp₁₇]

private theorem totient_250 : (250 : ℕ).totient = 100 := by
  have h₂ : Nat.Coprime 2 (5^3) := by decide
  rw [show (250 : ℕ) = 2*5^3 by decide, Nat.totient_mul h₂, Nat.totient_prime Nat.prime_two,
    show ((5 : ℕ)^3).totient = 5^2*(5-1) from Nat.totient_prime_pow_succ Nat.prime_five 2]
  decide

/-- The even squarefree length-three endpoint cannot have a nonsquarefree length-four
partner. On dividing out 2, the only possible odd core on the four-factor side is 5³,
and the resulting pair 238 and 250 fails the totient shift. -/
theorem no_even_squarefree_three_nonsquarefree_four_pair {n m : ℕ}
    (he : Even n) (hns : Squarefree n) (hms : ¬Squarefree m)
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) : False := by
  obtain ⟨a,ha⟩ := he
  have hna : n = 2*a := by omega
  have hns' : Squarefree (2*a) := hna ▸ hns
  have hca := Nat.coprime_of_squarefree_mul hns'
  have hoa := hca.odd_of_left
  have ham := Nat.odd_iff.mp hoa
  have hme : Even m := Nat.even_iff.mpr (by omega)
  obtain ⟨b,hb⟩ := hme
  have hmb : m = 2*b := by omega
  have hob : Odd b := Nat.odd_iff.mpr (by omega)
  have hcb := hob.coprime_two_left
  have has : Squarefree a := hns'.squarefree_of_dvd (dvd_mul_left a 2)
  have hbs : ¬Squarefree b := fun h => hms (hmb ▸ ((Nat.squarefree_mul hcb).mpr
    ⟨Nat.prime_two.squarefree,h⟩))
  have haz : a ≠ 0 := has.ne_zero
  have hbz : b ≠ 0 := by have := Nat.odd_iff.mp hob; omega
  have hal : a.primeFactorsList.length = 2 := by
    have hh := length_mul_two_of_ne_zero haz
    rw [hna] at hn
    omega
  have hbl : b.primeFactorsList.length = 3 := by
    have hh := length_mul_two_of_ne_zero hbz
    rw [hmb] at hm
    omega
  have ha1 : 1 < a := by
    by_contra! h
    interval_cases a <;> simp at hal
  have hap : ¬a.Prime := by
    intro hp
    simp [Nat.primeFactorsList_prime hp] at hal
  have hsem : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ a = p*q := by
    by_contra h
    have hh := A056777Closure.factor_count_of_nonsemiprime ha1 hap h
    omega
  obtain ⟨p,q,hp,hq,hapq⟩ := hsem
  have hpq : p ≠ q := by
    rintro rfl
    exact Nat.squarefree_iff_prime_squarefree.mp has p hp ⟨1, by simp [hapq]⟩
  have hsmall := (A056777Closure.excess_two_iff a).mpr ⟨p,q,hp,hq,hpq,hapq⟩
  have hcoreφ := hφ
  have hcoreσ := hσ
  rw [hna,hmb,Nat.totient_mul hca,Nat.totient_mul hcb,Nat.totient_prime Nat.prime_two] at hcoreφ
  norm_num at hcoreφ
  rw [hna,hmb,isMultiplicative_sigma.map_mul_of_coprime hca,
    isMultiplicative_sigma.map_mul_of_coprime hcb, show σ 1 2 = 3 by decide] at hcoreσ
  have hlarge : σ 1 b + b.totient = 2*b+6 ∨ σ 1 b + b.totient + 2 = 2*b := by omega
  obtain ⟨r,s,hr,hs,hbrs⟩ := A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hbl hbs
  by_cases hrs : r = s
  · subst s
    have hbr : b = r^3 := by simpa [pow_succ] using hbrs
    have hr5 : r = 5 := by
      rw [hbr, excess_cube hr] at hlarge
      have := hr.two_le
      omega
    subst r
    have hm250 : m = 250 := by omega
    have hex : σ 1 b + b.totient = 2*b+6 := by
      rw [hbr]
      exact excess_cube hr
    have hn238 : n = 238 := by omega
    rw [hn238, hm250, totient_238, totient_250] at hφ
    omega
  · rw [hbrs, excess_repeated hr hs hrs] at hlarge
    have hr₂ := hr.two_le
    have hs₂ := hs.two_le
    omega

/-- The only shapes remaining for three factors versus four factors are p²q versus r³s
or r²st, with distinct prime bases within each product. The smaller endpoint is arbitrary. -/
theorem remaining_shapes_three_four_pair {n m : ℕ}
    (hn : n.primeFactorsList.length = 3) (hm : m.primeFactorsList.length = 4)
    (hgap : n+12=m ∨ m+12=n)
    (hφ : n.totient+m=m.totient+n) (hσ : σ 1 n+m = σ 1 m+n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p^2*q ∧
      ((∃ r s : ℕ, r.Prime ∧ s.Prime ∧ r ≠ s ∧ m = r^3*s) ∨
        (∃ r s t : ℕ, r.Prime ∧ s.Prime ∧ t.Prime ∧
          r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ m = r^2*s*t)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  have hms : ¬Squarefree m := fun h => A056777MixedFour.no_length_three_squarefree_length_four_pair
    hn hm h hgap hφ hσ
  have hns : ¬Squarefree n := by
    intro h
    by_cases he : Even n
    · exact no_even_squarefree_three_nonsquarefree_four_pair he h hms hn hm hgap hφ hσ
    · have ho := Nat.not_even_iff_odd.mp he
      have hom : Odd m := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp ho; omega)
      have hc : 3 ≤ n.primeFactors.card := by
        rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup h.nodup_primeFactorsList, hn]
      exact A056777OddFour.no_squarefree_odd_four_pair ho hom h hc hm hgap hφ hσ
  obtain ⟨p,q,hp,hq,heq⟩ :=
    A056777RepeatedTriple.pow_two_mul_of_nonsquarefree_length_three hn hns
  have hpq : p ≠ q := by
    rintro rfl
    have heq' : n = p^3 := by simpa [pow_succ] using heq
    rw [heq'] at hgap hφ hσ
    exact A056777CubeFour.no_cube_four_pair hp hm hgap hφ hσ
  refine ⟨p,q,hp,hq,hpq,heq,?_⟩
  rcases A056777CubeFour.four_factor_shape hm with ⟨k,hk⟩ | h | h |
    ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm'⟩
  · exfalso
    rcases hgap with he | he
    · have hstep : σ 1 (n+12) = σ 1 n+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hn0 hstep).2
        (Or.inl ⟨k,he.trans hk⟩)
    · have hstep : σ 1 (m+12) = σ 1 m+12 := by rw [he]; omega
      exact (A056777Parity.no_square_shapes_of_sigma_step hm0 hstep).1 (Or.inl ⟨k,hk⟩)
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [heq,hm'] at hgap hφ hσ
    exact A056777MixedFour.no_mixed_four_gap_twelve hp hq hr hs ht hu hpq hrs hrt hru hst hsu htu
      hgap hφ hσ

end A056777ThreeFourShapes

#print axioms A056777ThreeFourShapes.no_even_squarefree_three_nonsquarefree_four_pair
#print axioms A056777ThreeFourShapes.remaining_shapes_three_four_pair
