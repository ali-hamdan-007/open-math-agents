import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777CubeSquarefreeTriple

private theorem excess_cube {p : ℕ} (hp : p.Prime) :
    σ 1 (p ^ 3) + (p ^ 3).totient = 2 * p ^ 3 + p + 1 := by
  have hsig : σ 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have htot : (p ^ 3).totient = p ^ 2 * (p - 1) := Nat.totient_prime_pow_succ hp 2
  rw [hsig, htot]
  have h₁ := hp.pos
  zify [h₁]
  ring

private theorem excess_squarefree_triple {r s t : ℕ} (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) :
    σ 1 (r * s * t) + (r * s * t).totient = 2 * (r * s * t) + 2 * (r + s + t) := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hσ {p : ℕ} (hp : p.Prime) : σ 1 p = p + 1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) hp
  rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁,
    isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,
    Nat.totient_prime hr, Nat.totient_prime hs, Nat.totient_prime ht, hσ hr, hσ hs, hσ ht]
  have h₁ := hr.pos
  have h₂ := hs.pos
  have h₃ := ht.pos
  zify [h₁, h₂, h₃]
  ring

/-- Equal excess for a prime cube and a squarefree triple makes the latter more
than twelve smaller. This excludes either orientation of the A056777 step. -/
theorem no_cube_squarefree_triple_at_distance_twelve {p r s t : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (he : σ 1 (p ^ 3) + (p ^ 3).totient + 2 * (r * s * t) =
      σ 1 (r * s * t) + (r * s * t).totient + 2 * p ^ 3) :
    r * s * t + 12 < p ^ 3 := by
  rw [excess_cube hp, excess_squarefree_triple hr hs ht hrs hrt hst] at he
  have hr2 := hr.two_le
  have hs2 := hs.two_le
  have ht2 := ht.two_le
  have hsum : p + 1 = 2 * (r + s + t) := by omega
  have hp3 : 3 ≤ p := by omega
  have hrp : r ≤ p - 1 := by omega
  have hsp : s ≤ p - 1 := by omega
  have htp : t ≤ p - 1 := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hrp hsp) htp
  have hp1 : 1 ≤ p := by omega
  zify [hp1] at hprod hp3 ⊢
  have hh : 9 ≤ (p : ℤ) * p := calc
    9 = (3 : ℤ) * 3 := by decide
    _ ≤ _ := mul_le_mul hp3 hp3 (by decide) (by omega)
  nlinarith [sq_nonneg ((p : ℤ) - 3)]

end A056777CubeSquarefreeTriple

#print axioms A056777CubeSquarefreeTriple.no_cube_squarefree_triple_at_distance_twelve
