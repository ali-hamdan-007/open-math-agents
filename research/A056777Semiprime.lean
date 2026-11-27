import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# The two-distinct-primes case of OEIS A056777

The totient equality alone forces a prime quadruple when both integers
are products of two primes. The distinct-prime case corresponds to the
forward direction of Choudhury and Wei, Theorem 2.2 (arXiv:2606.10331).

The hypothesis `htot` is the third conjunct of `OeisA56777.A n` in
Formal Conjectures. The conclusion unfolds `OeisA56777.ComesFromPrimeQuadruple n`.
These are stated explicitly here so the certificate only needs the Mathlib
modules listed above.
-/

namespace A056777

private theorem totient_mul_add_sum {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : (p * q).totient + (p + q) = p * q + 1 := by
  rw [Nat.totient_mul ((Nat.coprime_primes hp hq).mpr hpq),
    Nat.totient_prime hp, Nat.totient_prime hq]
  zify [hp.one_lt.le, hq.one_lt.le]
  ring

theorem primeQuadruple_of_sorted_prime_pairs {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s)
    (hprod : r * s = p * q + 12)
    (htot : (r * s).totient = (p * q).totient + 12) :
    r = p + 2 ∧ s = p + 6 ∧ q = p + 8 := by
  have hsum : p + q = r + s := by
    have h₁ := totient_mul_add_sum hp hq hpq.ne
    have h₂ := totient_mul_add_sum hr hs hrs.ne
    omega
  have hps : p < s := by omega
  have hfactorZ : ((r : ℤ) - p) * ((s : ℤ) - p) = 12 := by
    have hprodZ : (r : ℤ) * s = p * q + 12 := by exact_mod_cast hprod
    have hsumZ : (p : ℤ) + q = r + s := by exact_mod_cast hsum
    calc
      _ = (r : ℤ) * s - p * (r + s) + p * p := by ring
      _ = 12 := by rw [← hsumZ, hprodZ]; ring
  have hpr : p < r := by
    by_contra! hle
    have h₁ : (r : ℤ) - p ≤ 0 := by omega
    have h₂ : 0 ≤ (s : ℤ) - p := by omega
    have h₃ := mul_nonpos_of_nonpos_of_nonneg h₁ h₂
    rw [hfactorZ] at h₃
    omega
  have hp2 : p ≠ 2 := by
    intro hp2
    have hr2 : r ≠ 2 := by omega
    have hs2 : s ≠ 2 := by omega
    have hodd : (r * s) % 2 = 1 := by
      rw [Nat.mul_mod, hr.eq_two_or_odd.resolve_left hr2, hs.eq_two_or_odd.resolve_left hs2]
    rw [hp2] at hprod
    omega
  have hr2 : r ≠ 2 := by have := hp.two_le; omega
  have hs2 : s ≠ 2 := by have := hp.two_le; omega
  have hpOdd := hp.eq_two_or_odd.resolve_left hp2
  have hrOdd := hr.eq_two_or_odd.resolve_left hr2
  have hsOdd := hs.eq_two_or_odd.resolve_left hs2
  let a := r - p
  let b := s - p
  have ha : a + p = r := Nat.sub_add_cancel hpr.le
  have hb : b + p = s := Nat.sub_add_cancel hps.le
  have hfactor : a * b = 12 := by
    have hz : ((a * b : ℕ) : ℤ) = 12 := by
      push_cast
      have haZ : (a : ℤ) = (r : ℤ) - p := by omega
      have hbZ : (b : ℤ) = (s : ℤ) - p := by omega
      rw [haZ, hbZ, hfactorZ]
    exact_mod_cast hz
  have haPos : 0 < a := by omega
  have hab : a < b := by omega
  have haEven : a % 2 = 0 := by omega
  have hbEven : b % 2 = 0 := by omega
  have haBound : a ≤ 12 := Nat.le_of_dvd (by decide) ⟨b, hfactor.symm⟩
  have hOffsets : a = 2 ∧ b = 6 := by
    interval_cases a <;> omega
  omega

private theorem totient_sq_add_prime {p : ℕ} (hp : p.Prime) :
    (p * p).totient + p = p * p := by
  rw [← pow_two, Nat.totient_prime_pow_succ hp 1, pow_one]
  zify [hp.one_lt.le]
  ring

/-- Prime-square endpoints are impossible, so it is enough that both
integers are semiprime, without any distinctness condition. -/
theorem primeQuadruple_of_prime_products {n : ℕ}
    (htot : (n + 12).totient = n.totient + 12)
    (hn : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q)
    (hn12 : ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ n + 12 = r * s) :
    ∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 6).Prime ∧ (p + 8).Prime ∧ n = p * (p + 8) := by
  have ordered (m : ℕ) (hm : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q) :
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ q ∧ m = p * q := by
    obtain ⟨p, q, hp, hq, hm⟩ := hm
    by_cases h : p ≤ q
    · exact ⟨p, q, hp, hq, h, hm⟩
    · exact ⟨q, p, hq, hp, by omega, hm.trans (Nat.mul_comm _ _)⟩
  obtain ⟨p, q, hp, hq, hpq, heq⟩ := ordered n hn
  obtain ⟨r, s, hr, hs, hrs, heq12⟩ := ordered (n + 12) hn12
  have hprod : r * s = p * q + 12 := by rw [← heq12, heq]
  rw [heq12, heq] at htot
  by_cases hpq' : p = q <;> by_cases hrs' : r = s
  · subst q s
    have hp' := totient_sq_add_prime hp
    have hr' := totient_sq_add_prime hr
    have : r = p := by omega
    subst r
    omega
  · subst q
    have hp' := totient_sq_add_prime hp
    have hr' := totient_mul_add_sum hr hs hrs'
    have hsum : r + s = p + 1 := by omega
    have hl : 2 ≤ r := hr.two_le
    have hu : 2 ≤ s := hs.two_le
    have hle := Nat.mul_le_mul (show r ≤ p by omega) (show s ≤ p by omega)
    omega
  · subst s
    have hp' := totient_mul_add_sum hp hq hpq'
    have hr' := totient_sq_add_prime hr
    have hsum : r + 1 = p + q := by omega
    have hp2 := hp.two_le
    have hlt : p < q := lt_of_le_of_ne hpq hpq'
    have hlow := Nat.mul_le_mul (show q + 1 ≤ r by omega) (show q + 1 ≤ r by omega)
    have hmul : (p + 1) * q ≤ q * q := Nat.mul_le_mul_right q hlt
    rw [Nat.add_mul, Nat.one_mul] at hmul
    have hq4 : q < 4 := by nlinarith
    have hpval : p = 2 := by omega
    have hqval : q = 3 := by omega
    have hrval : r = 4 := by omega
    simp [hpval, hqval, hrval] at hprod
  · obtain ⟨rfl, rfl, rfl⟩ := primeQuadruple_of_sorted_prime_pairs hp hq hr hs
      (lt_of_le_of_ne hpq hpq') (lt_of_le_of_ne hrs hrs') hprod htot
    exact ⟨p, hp, hr, hs, hq, heq⟩

end A056777

#print axioms A056777.primeQuadruple_of_prime_products
