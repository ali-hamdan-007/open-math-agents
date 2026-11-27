import A056777Parity
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubeFour

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa using sigma_one_apply_prime_pow (i := 1) hp

private theorem sigma_square {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
  simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]

private theorem sigma_cube {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
  simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, pow_one, zero_add]

private theorem excess_cube {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 3) + (p ^ 3).totient = 2 * p ^ 3 + p + 1 := by
  rw [sigma_cube hp, show (p ^ 3).totient = p ^ 2 * (p - 1) from Nat.totient_prime_pow_succ hp 2]
  have hp₁ := hp.pos
  zify [hp₁]
  ring

private theorem excess_cube_mul_prime {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hne : r ≠ s) :
    σ 1 (r ^ 3 * s) + (r ^ 3 * s).totient =
      2 * (r ^ 3 * s) + ((r + 1) * s + 2 * r ^ 2 + r + 1) := by
  have hc := ((Nat.coprime_primes hr hs).mpr hne).pow_left 3
  rw [isMultiplicative_sigma.map_mul_of_coprime hc, sigma_cube hr, sigma_prime hs,
    Nat.totient_mul hc, show (r ^ 3).totient = r ^ 2 * (r - 1) from Nat.totient_prime_pow_succ hr 2,
    Nat.totient_prime hs]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  zify [hr₁, hs₁]
  ring

private theorem excess_square_mul_primes {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r ^ 2 * s * t) + (r ^ 2 * s * t).totient =
      2 * (r ^ 2 * s * t) + (s * t + (2*r+1)*(s+t) + 2*r^2 + 1) := by
  have hc₁ := ((Nat.coprime_primes hr hs).mpr hrs).pow_left 2
  have hc₂ := (((Nat.coprime_primes hr ht).mpr hrt).pow_left 2).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hφ : (r ^ 2).totient = r * (r - 1) := by
    simpa using (Nat.totient_prime_pow_succ hr 1)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₂, isMultiplicative_sigma.map_mul_of_coprime hc₁,
    sigma_square hr, sigma_prime hs, sigma_prime ht,
    Nat.totient_mul hc₂, Nat.totient_mul hc₁, hφ, Nat.totient_prime hs, Nat.totient_prime ht]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  zify [hr₁, hs₁, ht₁]
  ring

private theorem excess_four_primes {r s t u : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hu : u.Prime) (hrs : r ≠ s) (hrt : r ≠ t) (hru : r ≠ u) (hst : s ≠ t) (hsu : s ≠ u)
    (htu : t ≠ u) :
    σ 1 (r*s*t*u) + (r*s*t*u).totient =
      2*(r*s*t*u)+2*(r*s+r*t+r*u+s*t+s*u+t*u)+2 := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := (((Nat.coprime_primes hr hu).mpr hru).mul_left
    ((Nat.coprime_primes hs hu).mpr hsu)).mul_left ((Nat.coprime_primes ht hu).mpr htu)
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₃,
    isMultiplicative_sigma.map_mul_of_coprime hc₂, isMultiplicative_sigma.map_mul_of_coprime hc₁,
    sigma_prime hr, sigma_prime hs, sigma_prime ht, sigma_prime hu, Nat.totient_mul hc₃,
    Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_prime hr, Nat.totient_prime hs,
    Nat.totient_prime ht, Nat.totient_prime hu]
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  have hu₁ := hu.pos
  zify [hr₁, hs₁, ht₁, hu₁]
  ring

theorem four_factor_shape {n : ℕ} (h : n.primeFactorsList.length = 4) :
    (∃ k, n = k^2) ∨
    (∃ r s, r.Prime ∧ s.Prime ∧ r ≠ s ∧ n = r^3*s) ∨
    (∃ r s t, r.Prime ∧ s.Prime ∧ t.Prime ∧ r ≠ s ∧ r ≠ t ∧ s ≠ t ∧ n = r^2*s*t) ∨
    ∃ r s t u, r.Prime ∧ s.Prime ∧ t.Prime ∧ u.Prime ∧
      r ≠ s ∧ r ≠ t ∧ r ≠ u ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u ∧ n = r*s*t*u := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  have hprod := Nat.prod_primeFactorsList hn
  obtain ⟨a,b,c,d,he⟩ : ∃ a b c d, n.primeFactorsList = [a,b,c,d] := by
    generalize hl : n.primeFactorsList = l at h ⊢
    rcases l with _ | ⟨a,l⟩
    · simp at h
    rcases l with _ | ⟨b,l⟩
    · simp at h
    rcases l with _ | ⟨c,l⟩
    · simp at h
    rcases l with _ | ⟨d,l⟩
    · simp at h
    rcases l with _ | ⟨e,l⟩
    · exact ⟨a,b,c,d,rfl⟩
    · simp at h
  have ha := Nat.prime_of_mem_primeFactorsList (n := n) (p := a) (by simp [he])
  have hb := Nat.prime_of_mem_primeFactorsList (n := n) (p := b) (by simp [he])
  have hc := Nat.prime_of_mem_primeFactorsList (n := n) (p := c) (by simp [he])
  have hd := Nat.prime_of_mem_primeFactorsList (n := n) (p := d) (by simp [he])
  have hsort := (Nat.primeFactorsList_sorted n).pairwise
  simp only [he, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false] at hsort
  have hab : a ≤ b := hsort.1 b (Or.inl rfl)
  have hbc : b ≤ c := hsort.2.1 c (Or.inl rfl)
  have hcd : c ≤ d := hsort.2.2.1 d rfl
  simp only [he, List.prod_cons, List.prod_nil, mul_one] at hprod
  by_cases hab' : a = b <;> by_cases hbc' : b = c <;> by_cases hcd' : c = d
  · left
    refine ⟨a*a, ?_⟩
    subst b c d
    rw [← hprod]
    ring
  · right; left
    refine ⟨a,d,ha,hd,by omega,?_⟩
    subst b c
    rw [← hprod]
    ring
  · left
    refine ⟨a*c, ?_⟩
    subst b d
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨a,c,d,ha,hc,hd,by omega,by omega,hcd',?_⟩
    subst b
    rw [← hprod]
    ring
  · right; left
    refine ⟨b,a,hb,ha,Ne.symm hab',?_⟩
    subst c d
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨b,a,d,hb,ha,hd,Ne.symm hab',by omega,by omega,?_⟩
    subst c
    rw [← hprod]
    ring
  · right; right; left
    refine ⟨c,a,b,hc,ha,hb,by omega,Ne.symm hbc',hab',?_⟩
    subst d
    rw [← hprod]
    ring
  · right; right; right
    refine ⟨a,b,c,d,ha,hb,hc,hd,hab',by omega,by omega,hbc',by omega,hcd',?_⟩
    rw [← hprod]
    ring

private theorem product_three_far_below_cube {p a b c : ℕ} (hp : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) :
    a*b*c + 12 < p^3 := by
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
  nlinarith only [hprod, hh, hq]

/-- No odd prime cube is twelve from a four-factor number satisfying both jump conditions.
The equality of arithmetic defects treats both orientations at once. -/
theorem no_odd_cube_four_pair {p m : ℕ} (hp : p.Prime) (ho : Odd p)
    (hl : m.primeFactorsList.length = 4)
    (hgap : p^3 + 12 = m ∨ m + 12 = p^3)
    (hφ : (p^3).totient + m = m.totient + p^3)
    (hσ : σ 1 (p^3) + m = σ 1 m + p^3) : False := by
  have hpo := Nat.odd_iff.mp ho
  have hp₃ : 3 ≤ p := by have := hp.two_le; omega
  have hpcube : Odd (p^3) := by simpa [pow_succ, Nat.odd_mul] using ho
  have hσeven : Even (σ 1 (p^3)) := by
    rw [sigma_cube hp]
    have h₂ := Nat.odd_iff.mp (show Odd (p^2) by simpa [pow_two, Nat.odd_mul] using ho)
    have h₃ := Nat.odd_iff.mp hpcube
    exact Nat.even_iff.mpr (by omega)
  have he : σ 1 m + m.totient = 2*m + p + 1 := by
    have := excess_cube hp
    omega
  rcases four_factor_shape hl with ⟨k,hk⟩ | ⟨r,s,hr,hs,hne,hm⟩ |
    ⟨r,s,t,hr,hs,ht,hrs,hrt,hst,hm⟩ | ⟨r,s,t,u,hr,hs,ht,hu,hrs,hrt,hru,hst,hsu,htu,hm⟩
  · have hm0 : m ≠ 0 := by rintro rfl; simp at hl
    have hodd := Nat.odd_iff.mp ((A056777Parity.odd_sigma_iff_square_or_twice_square hm0).mpr
      (Or.inl ⟨k,hk⟩))
    have := Nat.even_iff.mp hσeven
    omega
  · rw [hm, excess_cube_mul_prime hr hs hne] at he
    have h : p = (r+1)*s + 2*r^2 + r := by omega
    have hr2 := hr.two_le
    have hs2 := hs.two_le
    have h₁ : r^2 < p := by nlinarith
    have h₂ : r < p := by nlinarith
    have h₃ : s < p := by nlinarith
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ h₃
    have hmul : r^3*s = r^2*r*s := by ring
    rw [hm, hmul] at hgap
    omega
  · rw [hm, excess_square_mul_primes hr hs ht hrs hrt hst] at he
    have h : p = s*t + (2*r+1)*(s+t) + 2*r^2 := by omega
    have h₁ : r^2 < p := by have := hr.two_le; nlinarith
    have h₂ : s < p := by have := ht.two_le; have := hs.two_le; nlinarith
    have h₃ : t < p := by have := hs.two_le; have := ht.two_le; nlinarith
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ h₃
    rw [hm] at hgap
    omega
  · rw [hm, excess_four_primes hr hs ht hu hrs hrt hru hst hsu htu] at he
    have h₁ : r*s < p := by omega
    have h₂ : t*u < p := by omega
    have hlt := product_three_far_below_cube hp₃ h₁ h₂ (show 1 < p by omega)
    have hmul : r*s*t*u = (r*s)*(t*u)*1 := by ring
    rw [hm, hmul] at hgap
    omega

/-- A prime cube cannot be paired with an endpoint of total prime multiplicity four. -/
theorem no_cube_four_pair {p m : ℕ} (hp : p.Prime)
    (hl : m.primeFactorsList.length = 4)
    (hgap : p^3 + 12 = m ∨ m + 12 = p^3)
    (hφ : (p^3).totient + m = m.totient + p^3)
    (hσ : σ 1 (p^3) + m = σ 1 m + p^3) : False := by
  rcases hp.eq_two_or_odd with rfl | ho
  · have hm : m = 20 := by norm_num at hgap; omega
    subst m
    have hp5 : Nat.Prime 5 := Nat.prime_five
    have hlen := (Nat.perm_primeFactorsList_mul (a := 2^2) (b := 5)
      (by decide) (by decide)).length_eq
    rw [show (2 : ℕ)^2*5 = 20 by decide, Nat.prime_two.primeFactorsList_pow,
      Nat.primeFactorsList_prime hp5, List.length_append, List.length_replicate] at hlen
    change (20 : ℕ).primeFactorsList.length = 3 at hlen
    omega
  · exact no_odd_cube_four_pair hp (Nat.odd_iff.mpr ho) hl hgap hφ hσ

end A056777CubeFour

#print axioms A056777CubeFour.no_odd_cube_four_pair
#print axioms A056777CubeFour.no_cube_four_pair
