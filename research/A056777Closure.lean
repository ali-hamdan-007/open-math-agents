import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Tactic.NormNum

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Closure

private theorem sigma_prime {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
  simpa using sigma_one_apply_prime_pow (i := 1) hp

private theorem le_sigma (n : ℕ) (hn : 1 < n) : n + 1 ≤ σ 1 n := by
  rw [sigma_one_apply]
  calc
    n + 1 = ∑ d ∈ ({n, 1} : Finset ℕ), d := by simp [show n ≠ 1 by omega]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> exact Nat.mem_divisors.mpr ⟨by simp, by omega⟩) (by omega)

private theorem lt_sigma_of_not_prime (n : ℕ) (hn : 1 < n) (hp : ¬n.Prime) :
    n + 2 < σ 1 n := by
  obtain ⟨p, hprime, hdiv⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  have hne : p ≠ n := fun h => hp (h ▸ hprime)
  have hp1 := hprime.one_lt
  have : n + p + 1 ≤ σ 1 n := by
    rw [sigma_one_apply]
    calc
      n + p + 1 = ∑ d ∈ ({n, p, 1} : Finset ℕ), d := by
        simp [show n ≠ 1 by omega, show n ≠ p by omega, hprime.ne_one, add_assoc]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (by intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            rcases hx with rfl | rfl | rfl <;>
              exact Nat.mem_divisors.mpr ⟨by first | exact hdiv | simp, by omega⟩) (by omega)
  omega

/-- The excess of the sum of the divisor sum and the totient for a prime power. -/
private theorem prime_pow_excess (p k : ℕ) (hp : p.Prime) :
    σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient =
      2 * p ^ (k + 2) + ∑ j ∈ Finset.range (k + 1), p ^ j := by
  rw [sigma_one_apply_prime_pow hp, totient_prime_pow_succ hp,
    Finset.sum_range_succ, Finset.sum_range_succ, pow_succ p (k + 1)]
  have h : p - 1 + 1 = p := by have := hp.one_lt; omega
  have hh := congrArg (fun x : ℕ => p ^ (k + 1) * x) h
  simp only [Nat.mul_add, mul_one] at hh
  omega

/-- The divisor sum and totient together are at least twice the argument. -/
private theorem le_sigma_add_totient (n : ℕ) : 2 * n ≤ σ 1 n + n.totient := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    rcases k with _ | _ | k
    · omega
    · rw [show 0 + 1 = 1 by rfl, pow_one]
      rw [sigma_prime hp, totient_prime hp]
      have := hp.one_lt
      omega
    · change 2 * p ^ (k + 2) ≤ σ 1 (p ^ (k + 2)) + (p ^ (k + 2)).totient
      rw [prime_pow_excess p k hp]
      omega
  | coprime a b ha hb hc iha ihb =>
    have hsa := le_sigma a ha
    have hsb := le_sigma b hb
    have hta := Nat.totient_lt a ha
    have htb := Nat.totient_lt b hb
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc]
    have hprod := Nat.mul_le_mul iha ihb
    have hdiff := mul_nonneg
      (show 0 ≤ (σ 1 a : ℤ) - a.totient by omega)
      (show 0 ≤ (σ 1 b : ℤ) - b.totient by omega)
    zify at hprod ⊢
    nlinarith

/-- A positive integer has excess two precisely when it is a product of distinct primes. -/
theorem excess_two_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 2 ↔
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one] at h
        rw [sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · rw [prime_pow_excess p 0 hp] at h
        simp at h
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 2 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hforce (x y : ℕ) (hx : ¬x.Prime) (hx1 : 1 < x) (hy1 : 1 < y) :
          8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) := by
        have hsx := lt_sigma_of_not_prime x hx1 hx
        have hsy := le_sigma y hy1
        have htx := Nat.totient_lt x hx1
        have hty := Nat.totient_lt y hy1
        exact mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
      have hpa : a.Prime := by
        by_contra hn
        linarith only [h, hprod, hforce a b hn ha hb]
      have hpb : b.Prime := by
        by_contra hn
        have he := hforce b a hn hb ha
        rw [mul_comm] at he
        linarith only [h, hprod, he]
      exact ⟨a, b, hpa, hpb, ((Nat.coprime_primes hpa hpb).mp hc), rfl⟩
  · rintro ⟨p, q, hp, hq, hne, rfl⟩
    have hc := (Nat.coprime_primes hp hq).mpr hne
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc,
      sigma_prime hp, sigma_prime hq, Nat.totient_prime hp, Nat.totient_prime hq]
    zify [hp.pos, hq.pos]
    ring


/-- Excess one classifies squares of primes. -/
theorem excess_one_iff (n : ℕ) :
    σ 1 n + n.totient = 2 * n + 1 ↔ ∃ p : ℕ, p.Prime ∧ n = p ^ 2 := by
  constructor
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp at h
    | one => simp at h
    | prime_pow p k hp hk =>
      rcases k with _ | _ | _ | k
      · omega
      · rw [show 0 + 1 = 1 by rfl, pow_one, sigma_prime hp, totient_prime hp] at h
        have := hp.one_lt
        omega
      · exact ⟨p, hp, rfl⟩
      · change σ 1 (p ^ ((k + 1) + 2)) + (p ^ ((k + 1) + 2)).totient =
          2 * p ^ ((k + 1) + 2) + 1 at h
        rw [prime_pow_excess p (k + 1) hp] at h
        have hs : 1 + p ≤ ∑ j ∈ Finset.range (k + 1 + 1), p ^ j := by
          calc
            1 + p = ∑ j ∈ Finset.range 2, p ^ j := by simp [Finset.sum_range_succ]
            _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.range_subset_range.mpr (by omega)) (by omega)
        have := hp.one_lt
        omega
    | coprime a b ha hb hc _ _ =>
      rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.totient_mul hc] at h
      have hprod := Nat.mul_le_mul (le_sigma_add_totient a) (le_sigma_add_totient b)
      zify at h hprod
      have hsa := le_sigma a ha
      have hsb := le_sigma b hb
      have hta := Nat.totient_lt a ha
      have htb := Nat.totient_lt b hb
      have hdiff : 4 ≤ ((σ 1 a : ℤ) - a.totient) * ((σ 1 b : ℤ) - b.totient) :=
        mul_le_mul (show (2 : ℤ) ≤ σ 1 a - (a.totient : ℤ) by omega)
          (show (2 : ℤ) ≤ σ 1 b - (b.totient : ℤ) by omega) (by decide) (by omega)
      linarith only [h, hprod, hdiff]
  · rintro ⟨p, hp, rfl⟩
    simpa using prime_pow_excess p 0 hp

private theorem no_prime_squares_at_distance_twelve {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ^ 2 + 12 = q ^ 2) : False := by
  have hp2 := hp.two_le
  have hpq : p < q := by
    by_contra! hle
    have := Nat.mul_le_mul hle hle
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : q = p + 1
  · rw [heq] at h
    have hh : 2 * p + 1 = 12 := by nlinarith
    omega
  · have hle : p + 2 ≤ q := by omega
    have hsq := Nat.mul_le_mul hle hle
    have hp_le : p ≤ 2 := by nlinarith
    have hq_le : q ≤ 4 := by
      have hp_eq : p = 2 := by omega
      rw [hp_eq] at h
      by_contra! H
      have hh := Nat.mul_le_mul H H
      norm_num at h
      nlinarith
    have hq_eq : q = 4 := by omega
    exact (by decide : ¬Nat.Prime 4) (hq_eq ▸ hq)

private theorem ordered_factors {n : ℕ}
    (h : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q := by
  obtain ⟨p, q, hp, hq, hne, hn⟩ := h
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨p, q, hp, hq, h, hn⟩
  · exact ⟨q, p, hq, hp, h, by simpa [mul_comm] using hn⟩

private theorem sum_eq_of_totient {n p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (hn : n = p * q) (hm : n + 12 = r * s)
    (ht : (n + 12).totient = n.totient + 12) :
    p + q = r + s := by
  rw [hm, hn, Nat.totient_mul ((Nat.coprime_primes hr hs).mpr hrs.ne),
    Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq.ne),
    Nat.totient_prime hp, Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs] at ht
  zify [hp.pos, hq.pos, hr.pos, hs.pos] at hn hm ht ⊢
  linarith

/-- If either argument has excess two, the simultaneous totient and divisor-sum
increments by twelve force the pair to come from a prime quadruple. -/
theorem prime_quadruple_of_one_excess_two {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (he : σ 1 n + n.totient = 2 * n + 2 ∨
      σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  have he₁ : σ 1 n + n.totient = 2 * n + 2 := by omega
  have he₂ : σ 1 (n + 12) + (n + 12).totient = 2 * (n + 12) + 2 := by omega
  obtain ⟨p, q, hp, hq, hpq, hn⟩ := ordered_factors ((excess_two_iff n).mp he₁)
  obtain ⟨r, s, hr, hs', hrs, hm⟩ := ordered_factors ((excess_two_iff (n + 12)).mp he₂)
  have hsum := sum_eq_of_totient hp hq hr hs' hpq hrs hn hm ht
  have hpr : p < r := by
    by_contra! h
    have hsr : (r : ℤ) ≤ s := by exact_mod_cast hrs.le
    have hrp : (r : ℤ) ≤ p := by exact_mod_cast h
    zify at hn hm hsum
    have H := mul_nonneg (show 0 ≤ (p : ℤ) - r by omega)
      (show 0 ≤ (q : ℤ) - r by omega)
    linarith only [hn, hm, hsum, H, show
      (p : ℤ) * q - r * s = ((p : ℤ) - r) * (q - r) from by
        linear_combination (r : ℤ) * hsum]
  have hq2 : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hr2 : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by
    have := hp.two_le
    omega)
  have hs2 : s % 2 = 1 := hs'.eq_two_or_odd.resolve_left (by
    have := hr.two_le
    omega)
  have hp2 : p % 2 = 1 := by omega
  let d := r - p
  let e := q - r
  have hd : 0 < d := by dsimp [d]; omega
  have hde : d ≤ e := by dsimp [d, e]; omega
  have hdp : d % 2 = 0 := by dsimp [d]; omega
  have hprod : d * e = 12 := by
    have hd' : d + p = r := by dsimp [d]; omega
    have he' : e + r = q := by dsimp [e]; omega
    have hs'' : s = p + e := by omega
    rw [← hd'] at he'
    rw [← hd', hs''] at hm
    rw [← he'] at hn
    nlinarith only [hn, hm]
  have hd4 : d < 4 := by
    by_contra! hd4
    have hm16 : 4 * 4 ≤ d * e := Nat.mul_le_mul hd4 (hd4.trans hde)
    omega
  have hd2 : d = 2 := by omega
  have he6 : e = 6 := by rw [hd2] at hprod; omega
  have hrp : r = p + 2 := by dsimp [d] at hd2; omega
  have hsp : s = p + 6 := by dsimp [e] at he6; omega
  have hqp : q = p + 8 := by dsimp [e] at he6; omega
  refine ⟨p, hp, hrp ▸ hr, hsp ▸ hs', hqp ▸ hq, ?_⟩
  simpa [hqp] using hn

/-- The prime-quadruple conjecture holds whenever either member of the pair
is semiprime, including the case of a square of a prime. -/
theorem prime_quadruple_of_one_semiprime {n : ℕ}
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hp : (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) ∨
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n + 12 = p * q) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  rcases hp with ⟨p, q, hp, hq, hn⟩ | ⟨p, q, hp, hq, hn⟩
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff n).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff (n + 12)).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hp hq (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inl ((excess_two_iff n).mpr ⟨p, q, hp, hq, h, hn⟩))
  · by_cases h : p = q
    · subst q
      have he := (excess_one_iff (n + 12)).mpr ⟨p, hp, by simpa [pow_two] using hn⟩
      obtain ⟨q, hq, hm⟩ := (excess_one_iff n).mp (by omega)
      exact (no_prime_squares_at_distance_twelve hq hp (by simp_all [pow_two])).elim
    · exact prime_quadruple_of_one_excess_two ht hs
        (Or.inr ((excess_two_iff (n + 12)).mpr ⟨p, q, hp, hq, h, hn⟩))

theorem factor_count_of_nonsemiprime {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (hs : ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q) :
    3 ≤ n.primeFactorsList.length := by
  have hprod := Nat.prod_primeFactorsList (n := n) (by omega)
  have hprime {p : ℕ} (hm : p ∈ n.primeFactorsList) := Nat.prime_of_mem_primeFactorsList hm
  cases h : n.primeFactorsList with
  | nil => simp [h] at hprod; omega
  | cons p tail =>
    cases tail with
    | nil =>
      have hp' := hprime (p := p) (by simp [h])
      simp [h] at hprod
      exact (hp (hprod ▸ hp')).elim
    | cons q tail =>
      cases tail with
      | nil =>
        exact (hs ⟨p, q, hprime (by simp [h]), hprime (by simp [h]),
          by simpa [h] using hprod.symm⟩).elim
      | cons r tail => simp

/-- A counterexample to the converse for A056777 must have at least three
prime factors, counted with multiplicity, in both positions. -/
theorem factor_count_of_counterexample {n : ℕ} (hn : 1 < n) (hp : ¬n.Prime)
    (ht : (n + 12).totient = n.totient + 12)
    (hs : σ 1 (n + 12) = σ 1 n + 12)
    (hc : ¬∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧
      (p + 8).Prime ∧ n = p * (p + 8)) :
    3 ≤ n.primeFactorsList.length ∧ 3 ≤ (n + 12).primeFactorsList.length := by
  have hm : ¬(n + 12).Prime := by
    intro hm
    rw [sigma_prime hm] at hs
    have := lt_sigma_of_not_prime n hn hp
    omega
  exact ⟨factor_count_of_nonsemiprime hn hp
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inl h))),
    factor_count_of_nonsemiprime (by omega) hm
      (fun h => hc (prime_quadruple_of_one_semiprime ht hs (Or.inr h)))⟩

/-- The low values of the excess for an odd squarefree number are zero and two. -/
theorem low_excess_of_odd_squarefree (n : ℕ) (ho : Odd n) (hs : Squarefree n) :
    σ 1 n + n.totient = 2 * n ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient := by
  suffices h : n = 1 ∨ n.Prime ∨ σ 1 n + n.totient = 2 * n + 2 ∨
      2 * n + 10 ≤ σ 1 n + n.totient by
    rcases h with rfl | hp | h | h
    · left; simp
    · left
      rw [sigma_prime hp, Nat.totient_prime hp]
      have := hp.one_lt
      omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp at ho
  | one => exact Or.inl rfl
  | prime_pow p k hp hk =>
    have h := hs.natFactorization_le_one p
    rw [hp.factorization_pow, Finsupp.single_eq_same] at h
    have h1 : k = 1 := by omega
    subst k
    exact Or.inr (Or.inl (by simpa using hp))
  | coprime a b ha hb hc iha ihb =>
    obtain ⟨hoa, hob⟩ := Nat.odd_mul.mp ho
    have hsa := hs.squarefree_of_dvd (dvd_mul_right a b)
    have hsb := hs.squarefree_of_dvd (dvd_mul_left b a)
    by_cases hab : a.Prime ∧ b.Prime
    · exact Or.inr (Or.inr (Or.inl ((excess_two_iff _).mpr
        ⟨a, b, hab.1, hab.2, (Nat.coprime_primes hab.1 hab.2).mp hc, rfl⟩)))
    · have hhelper (x y : ℕ) (hx : 1 < x) (hy : 1 < y) (hyod : Odd y)
          (hcop : x.Coprime y) (hnp : ¬x.Prime)
          (hi : x = 1 ∨ x.Prime ∨ σ 1 x + x.totient = 2 * x + 2 ∨
            2 * x + 10 ≤ σ 1 x + x.totient) :
          2 * (x * y) + 10 ≤ σ 1 (x * y) + (x * y).totient := by
        have hDx : 2 * x + 2 ≤ σ 1 x + x.totient := by
          rcases hi with h | h | h | h
          · omega
          · exact (hnp h).elim
          · omega
          · omega
        have hDy := le_sigma_add_totient y
        have hy3 : 3 ≤ y := by have := Nat.odd_iff.mp hyod; omega
        have hprod := Nat.mul_le_mul hDx hDy
        have hσx := lt_sigma_of_not_prime x hx hnp
        have hσy := le_sigma y hy
        have htx := Nat.totient_lt x hx
        have hty := Nat.totient_lt y hy
        have hdiff : 8 ≤ ((σ 1 x : ℤ) - x.totient) * ((σ 1 y : ℤ) - y.totient) :=
          mul_le_mul (show (4 : ℤ) ≤ σ 1 x - (x.totient : ℤ) by omega)
            (show (2 : ℤ) ≤ σ 1 y - (y.totient : ℤ) by omega) (by decide) (by omega)
        rw [isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.totient_mul hcop]
        zify at hprod hy3 ⊢
        linarith only [hprod, hy3, hdiff]
      refine Or.inr (Or.inr (Or.inr ?_))
      by_cases hap : a.Prime
      · have hbp : ¬b.Prime := fun hp => hab ⟨hap, hp⟩
        simpa [mul_comm] using hhelper b a hb ha hoa hc.symm hbp (ihb hob hsb)
      · exact hhelper a b ha hb hob hc hap (iha hoa hsa)

end A056777Closure

#print axioms A056777Closure.excess_two_iff
#print axioms A056777Closure.prime_quadruple_of_one_excess_two
#print axioms A056777Closure.prime_quadruple_of_one_semiprime
#print axioms A056777Closure.factor_count_of_counterexample
#print axioms A056777Closure.low_excess_of_odd_squarefree
