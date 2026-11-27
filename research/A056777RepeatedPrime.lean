import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Injectivity of the totient deficit and divisor surplus for prime products `p²q`

For distinct primes `p` and `q`, the values of `n - φ(n)` and `σ(n) - n`
determine both primes when `n = p²q`. In particular, two such numbers at
distance 12 cannot satisfy both gap equalities of OEIS A056777.

Integer-valued differences avoid truncated subtraction.
-/

namespace A056777

open scoped ArithmeticFunction.sigma

/-- The amount by which the totient falls below its argument. -/
def totientDeficit (n : ℕ) : ℤ := (n : ℤ) - n.totient

/-- The sum of the proper divisors of the argument. -/
def divisorSurplus (n : ℕ) : ℤ := (σ 1 n : ℤ) - n

theorem totientDeficit_prime_sq_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    totientDeficit (p ^ 2 * q) = (p : ℤ) ^ 2 + p * (q : ℤ) - p := by
  unfold totientDeficit
  have hc : (p ^ 2).Coprime q := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  rw [Nat.totient_mul hc, Nat.totient_prime_pow_succ hp 1, pow_one, Nat.totient_prime hq]
  push_cast [hp.one_lt.le, hq.one_lt.le]
  ring

theorem divisorSurplus_prime_sq_mul_prime {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    divisorSurplus (p ^ 2 * q) = (p : ℤ) ^ 2 + ((p : ℤ) + 1) * (q + 1) := by
  unfold divisorSurplus
  have hc : (p ^ 2).Coprime q := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hsq : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp]
    simp [Finset.sum_range_succ]
  have hq' : σ 1 q = 1 + q := by
    simpa [Finset.sum_range_succ] using
      (ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hq)
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hc, hsq, hq']
  push_cast
  ring

/-- The two arithmetic invariants identify the ordered primes in a product `p²q`. -/
theorem prime_sq_mul_prime_invariants_injective {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s)
    (hf : totientDeficit (p ^ 2 * q) = totientDeficit (r ^ 2 * s))
    (hg : divisorSurplus (p ^ 2 * q) = divisorSurplus (r ^ 2 * s)) :
    p = r ∧ q = s := by
  rw [totientDeficit_prime_sq_mul_prime hp hq hpq,
    totientDeficit_prime_sq_mul_prime hr hs hrs] at hf
  rw [divisorSurplus_prime_sq_mul_prime hp hq hpq,
    divisorSurplus_prime_sq_mul_prime hr hs hrs] at hg
  have hsum : (q : ℤ) + 2 * p = (s : ℤ) + 2 * r := by
    linear_combination hg - hf
  have hfactor : ((p : ℤ) - r) * ((q : ℤ) + 2 * p - p - r - 1) = 0 := by
    linear_combination hf - (r : ℤ) * hsum
  rcases mul_eq_zero.mp hfactor with heq | heq
  · have hpr : p = r := by omega
    omega
  · have hq' := hq.two_le
    have hs' := hs.two_le
    omega

/-- No two distinct-prime products of this shape satisfy both gap equalities at positive gap. -/
theorem no_positive_gap_prime_sq_mul_prime {p q r s d : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hd : 0 < d)
    (hprod : r ^ 2 * s = p ^ 2 * q + d)
    (htot : (r ^ 2 * s).totient = (p ^ 2 * q).totient + d)
    (hsigma : σ 1 (r ^ 2 * s) = σ 1 (p ^ 2 * q) + d) :
    False := by
  have hf : totientDeficit (p ^ 2 * q) = totientDeficit (r ^ 2 * s) := by
    simp only [totientDeficit, htot]
    rw [show (↑(r ^ 2 * s) : ℤ) = ↑(p ^ 2 * q + d) by exact_mod_cast hprod]
    push_cast
    omega
  have hg : divisorSurplus (p ^ 2 * q) = divisorSurplus (r ^ 2 * s) := by
    simp only [divisorSurplus, hsigma]
    rw [show (↑(r ^ 2 * s) : ℤ) = ↑(p ^ 2 * q + d) by exact_mod_cast hprod]
    push_cast
    omega
  obtain ⟨rfl, rfl⟩ := prime_sq_mul_prime_invariants_injective hp hq hr hs hpq hrs hf hg
  omega

#print axioms A056777.prime_sq_mul_prime_invariants_injective
#print axioms A056777.no_positive_gap_prime_sq_mul_prime

end A056777
