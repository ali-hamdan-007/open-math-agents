import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped ArithmeticFunction.sigma
open Nat Finset ArithmeticFunction

namespace A056777Parity

theorem geom_odd_mod_two {p : ℕ} (hp : p % 2 = 1) (k : ℕ) :
    (∑ i ∈ Finset.range k, p ^ i) % 2 = k % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.pow_mod, hp]
    simp [Nat.add_mod]

private theorem prime_pow_square_shape {p k : ℕ} (hp : p.Prime)
    (h : Odd (σ 1 (p ^ k))) :
    (∃ a : ℕ, p ^ k = a ^ 2) ∨ ∃ a : ℕ, p ^ k = 2 * a ^ 2 := by
  rcases hp.eq_two_or_odd with rfl | hpodd
  · by_cases hk : k % 2 = 0
    · left
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩
    · right
      exact ⟨2 ^ (k / 2), by rw [← pow_mul, ← pow_succ', show (k / 2 * 2).succ = k by omega]⟩
  · have ho := Nat.odd_iff.mp h
    rw [sigma_one_apply_prime_pow hp, geom_odd_mod_two hpodd] at ho
    left
    exact ⟨p ^ (k / 2), by rw [← pow_mul, show k / 2 * 2 = k by omega]⟩

/-- Odd divisor sums occur only for squares and twice squares. -/
theorem square_or_twice_square {n : ℕ} (h : Odd (σ 1 n)) :
    (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => left; exact ⟨0, by decide⟩
  | one => left; exact ⟨1, by decide⟩
  | prime_pow p k hp hk => exact prime_pow_square_shape hp h
  | coprime a b ha hb hc iha ihb =>
    rw [isMultiplicative_sigma.map_mul_of_coprime hc, Nat.odd_mul] at h
    rcases iha h.1 with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
      rcases ihb h.2 with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact Or.inl ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · exact Or.inr ⟨x * y, by ring⟩
    · have := Nat.dvd_gcd (dvd_mul_right 2 (x ^ 2)) (dvd_mul_right 2 (y ^ 2))
      rw [hc.gcd_eq_one] at this
      omega

private theorem geom_two_mod_two (k : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (2 : ℕ) ^ i) % 2 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, pow_succ', Nat.mul_mod]
    simp

private theorem odd_sigma_of_even_odd_prime_exponents (n : ℕ) (hn : n ≠ 0)
    (hf : ∀ p, p.Prime → p ≠ 2 → Even (n.factorization p)) :
    Odd (σ 1 n) := by
  rw [sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hn]
  simp only [Nat.mul_one]
  suffices h : ∀ s : Finset ℕ, s ⊆ n.primeFactors →
      Odd (∏ p ∈ s, ∑ i ∈ Finset.range (n.factorization p + 1), p ^ i) by
    exact h _ Subset.rfl
  intro s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    intro hsub
    have hprime := Nat.prime_of_mem_primeFactors (hsub (Finset.mem_insert_self p s))
    rw [Finset.prod_insert hp, Nat.odd_mul]
    refine ⟨?_, ih (fun q hq => hsub (Finset.mem_insert_of_mem hq))⟩
    rw [Nat.odd_iff]
    rcases hprime.eq_two_or_odd with hp' | hp'
    · rw [hp', geom_two_mod_two]
    · have hne : p ≠ 2 := by omega
      obtain ⟨k, hk⟩ := hf p hprime hne
      rw [geom_odd_mod_two hp', hk]
      omega

/-- A positive number has odd divisor sum precisely when it is a square or twice a square. -/
theorem odd_sigma_iff_square_or_twice_square {n : ℕ} (hn : n ≠ 0) :
    Odd (σ 1 n) ↔ (∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2 := by
  refine ⟨square_or_twice_square, ?_⟩
  intro h
  apply odd_sigma_of_even_odd_prime_exponents _ hn
  intro p _ hp
  rcases h with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    exact ⟨a.factorization p, by omega⟩
  · have ha : a ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul (by decide) (pow_ne_zero _ ha),
      Nat.prime_two.factorization, Nat.factorization_pow,
      Finsupp.add_apply, Finsupp.single_eq_of_ne hp, Finsupp.smul_apply, smul_eq_mul, zero_add]
    exact ⟨a.factorization p, by omega⟩

private theorem sq_mod_four (a : ℕ) : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 4)
  interval_cases (a % 4) <;> decide

private theorem sq_mod_eight (a : ℕ) : a ^ 2 % 8 = 0 ∨ a ^ 2 % 8 = 1 ∨ a ^ 2 % 8 = 4 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt a (by decide : 0 < 8)
  interval_cases (a % 8) <;> decide

private theorem not_sq_add_twelve_eq_twice_sq (a b : ℕ) : a ^ 2 + 12 ≠ 2 * b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : (a / 2) ^ 2 + 3 = 2 * (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem not_twice_sq_add_twelve_eq_sq (a b : ℕ) : 2 * a ^ 2 + 12 ≠ b ^ 2 := by
  intro h
  have ha : a % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have ha' : a % 2 = a % 4 % 2 := by omega
    rw [ha']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have hb : b % 2 = 0 := by
    have hh := congrArg (· % 4) h
    rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod a, Nat.pow_mod b] at hh
    have ha4 := Nat.mod_lt a (by decide : 0 < 4)
    have hb4 := Nat.mod_lt b (by decide : 0 < 4)
    have hb' : b % 2 = b % 4 % 2 := by omega
    rw [hb']
    interval_cases (a % 4) <;> interval_cases (b % 4) <;> (norm_num at hh) <;> decide
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have H : 2 * (a / 2) ^ 2 + 3 = (b / 2) ^ 2 := by
    nlinarith only [h, congrArg (· ^ 2) ha', congrArg (· ^ 2) hb']
  have hh := congrArg (· % 8) H
  rw [Nat.add_mod, Nat.mul_mod] at hh
  rcases sq_mod_eight (a / 2) with A | A | A <;>
    rcases sq_mod_eight (b / 2) with B | B | B <;> norm_num [A, B] at hh

private theorem eq_two_of_sq_add_twelve_eq_sq (a b : ℕ) (h : a ^ 2 + 12 = b ^ 2) : a = 2 := by
  have hab : a < b := by
    by_contra! hab
    have hh := Nat.mul_le_mul hab hab
    rw [pow_two, pow_two] at h
    omega
  by_cases heq : b = a + 1
  · subst b
    have hh : 2 * a + 1 = 12 := by nlinarith
    omega
  · have hle : a + 2 ≤ b := by omega
    have hsq := Nat.mul_le_mul hle hle
    have ha2 : a ≤ 2 := by nlinarith
    interval_cases a
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · have hb : 3 < b := by
        by_contra! hh
        have := Nat.mul_le_mul hh hh
        nlinarith
      have := Nat.mul_le_mul (show 4 ≤ b by omega) (show 4 ≤ b by omega)
      nlinarith
    · rfl

/-- Any pair satisfying the divisor-sum condition of A056777 has even divisor sums.
This excludes all square and twice-square endpoints with odd divisor sum. -/
theorem even_sigma_of_sigma_step {n : ℕ} (h : σ 1 (n + 12) = σ 1 n + 12) :
    Even (σ 1 n) ∧ Even (σ 1 (n + 12)) := by
  have he : Even (σ 1 n) := by
    by_contra hnot
    have h₁ : Odd (σ 1 n) := Nat.not_even_iff_odd.mp hnot
    have h₂ : Odd (σ 1 (n + 12)) := by rw [Nat.odd_iff, h]; have := Nat.odd_iff.mp h₁; omega
    rcases square_or_twice_square h₁ with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases square_or_twice_square h₂ with ⟨b, hb⟩ | ⟨b, hb⟩
    · have : a = 2 := eq_two_of_sq_add_twelve_eq_sq a b (ha ▸ hb)
      subst a
      subst n
      revert h
      decide
    · exact not_sq_add_twelve_eq_twice_sq a b (ha ▸ hb)
    · exact not_twice_sq_add_twelve_eq_sq a b (ha ▸ hb)
    · have h' : a ^ 2 + 6 = b ^ 2 := by omega
      have hh := congrArg (· % 4) h'
      rw [Nat.add_mod] at hh
      rcases sq_mod_four a with A | A <;> rcases sq_mod_four b with B | B <;>
        norm_num [A, B] at hh
  exact ⟨he, by rw [h]; exact he.add (by decide)⟩

/-- The divisor-sum condition alone excludes squares and twice squares at both endpoints. -/
theorem no_square_shapes_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (¬ ((∃ a : ℕ, n = a ^ 2) ∨ ∃ a : ℕ, n = 2 * a ^ 2)) ∧
    (¬ ((∃ a : ℕ, n + 12 = a ^ 2) ∨ ∃ a : ℕ, n + 12 = 2 * a ^ 2)) := by
  rw [← odd_sigma_iff_square_or_twice_square hn,
      ← odd_sigma_iff_square_or_twice_square (show n + 12 ≠ 0 by omega)]
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨fun ho => (Nat.not_even_iff_odd.mpr ho) he₁,
    fun ho => (Nat.not_even_iff_odd.mpr ho) he₂⟩

/-- Both arguments have some odd prime occurring to an odd exponent. -/
theorem odd_prime_exponents_of_sigma_step {n : ℕ} (hn : n ≠ 0)
    (h : σ 1 (n + 12) = σ 1 n + 12) :
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (n.factorization p)) ∧
    (∃ p, p.Prime ∧ p ≠ 2 ∧ Odd ((n + 12).factorization p)) := by
  have hexists {m : ℕ} (hm : m ≠ 0) (he : Even (σ 1 m)) :
      ∃ p, p.Prime ∧ p ≠ 2 ∧ Odd (m.factorization p) := by
    by_contra! hall
    apply (Nat.not_even_iff_odd.mpr (odd_sigma_of_even_odd_prime_exponents m hm ?_)) he
    intro p hp hp2
    by_contra hn
    exact hall p hp hp2 (Nat.not_even_iff_odd.mp hn)
  obtain ⟨he₁, he₂⟩ := even_sigma_of_sigma_step h
  exact ⟨hexists hn he₁, hexists (by omega) he₂⟩

end A056777Parity

#print axioms A056777Parity.even_sigma_of_sigma_step
#print axioms A056777Parity.no_square_shapes_of_sigma_step
#print axioms A056777Parity.odd_prime_exponents_of_sigma_step
