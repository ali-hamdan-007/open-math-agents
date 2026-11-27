import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open scoped ArithmeticFunction.sigma
open Nat ArithmeticFunction

namespace A056777MixedTriple

private theorem newton_two (r s t : ℕ) :
    3 * (r + s + t) * (r * s * t) ≤ (r * s + r * t + s * t) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((r : ℤ)*s - (r : ℤ)*t), sq_nonneg ((r : ℤ)*s - (s : ℤ)*t),
    sq_nonneg ((r : ℤ)*t - (s : ℤ)*t)]

private theorem newton_one (r s t : ℕ) :
    3 * (r * s + r * t + s * t) ≤ (r + s + t) ^ 2 := by
  zify
  nlinarith [sq_nonneg ((r : ℤ)-s), sq_nonneg ((r : ℤ)-t), sq_nonneg ((s : ℤ)-t)]

private theorem inconsistent_symmetric_bounds (p x S E₂ E₃ : ℤ)
    (hp : 3 ≤ p) (hx : 0 ≤ x) (hS : 2 * S = 2 * p + x)
    (he : E₂ = (2 * p + 1) * S - (p + 1)^2)
    (hgap : p^2 * (x - 1) - 12 ≤ E₃)
    (hN₁ : 3 * E₂ ≤ S^2) (hN₂ : 3 * S * E₃ ≤ E₂^2)
    (hp4 : p ≠ 4) : False := by
  have hf : 0 ≤ x^2 - (8*p + 6)*x - 8*p^2 + 12*p + 12 := by
    have h := congrArg (fun t : ℤ => t^2) hS
    have h' := congrArg (fun t : ℤ => (2*p+1)*t) hS
    nlinarith only [h, h', he, hN₁]
  have hxx : 8*p + 6 < x := by
    by_contra! h
    have hmul := mul_nonneg hx (show 0 ≤ 8*p + 6 - x by omega)
    have hquad := mul_nonneg (show 0 ≤ p - 3 by omega) (show 0 ≤ 8*p + 12 by omega)
    nlinarith only [hf, hmul, hquad, hp]
  have hSL : 5*p + 3 < S := by omega
  have hS0 : 0 ≤ S := by omega
  have hN : 3*S*(p^2*(2*S-2*p-1)-12) ≤ ((2*p+1)*S-(p+1)^2)^2 := by
    rw [← he]
    have hh : p^2 * (2*S - 2*p - 1) - 12 ≤ E₃ := by
      have h' : 2*S-2*p-1 = x-1 := by omega
      simpa [h'] using hgap
    have := mul_le_mul_of_nonneg_left hh (show 0 ≤ 3*S by omega)
    exact this.trans hN₂
  by_cases hp3 : p = 3
  · subst p
    have h18 : 18 < S := by omega
    have hquad := mul_nonneg (show 0 ≤ S - 18 by omega) (show 0 ≤ 5*S + 89 by omega)
    nlinarith only [hN, hquad]
  · have hp5 : 5 ≤ p := by omega
    have hp0 : 0 ≤ p := by omega
    have hp2 : 0 ≤ p^2 := sq_nonneg p
    have hA : p^2 ≤ 2*p^2-4*p-1 := by
      have := mul_nonneg hp0 (show 0 ≤ p-5 by omega)
      nlinarith
    have hB : -2*p^3 ≤ -2*p^3+7*p^2+8*p-34 := by
      nlinarith
    have hp1 : (p + 1)^2 ≤ 2*p^2 := by
      have := mul_nonneg (show 0 ≤ p-3 by omega) (show 0 ≤ p by omega)
      nlinarith
    have hC : (p+1)^4 ≤ 4*p^4 := by
      have hh := mul_le_mul hp1 hp1 (sq_nonneg _) (by positivity : 0 ≤ 2*p^2)
      nlinarith only [hh]
    have hA' := mul_le_mul_of_nonneg_right hA (sq_nonneg S)
    have hB' := mul_le_mul_of_nonneg_right hB hS0
    have hS' : 5*p ≤ S := by omega
    have hS'' : 0 ≤ S*(S-5*p) := mul_nonneg hS0 (by omega)
    have h1 := mul_nonneg hp2 hS''
    have h2 := mul_nonneg (show 0 ≤ p^3 by positivity) (show 0 ≤ S-5*p by omega)
    have h3 : 0 < p^4 := by positivity
    nlinarith only [hN, hA', hB', hC, h1, h2, h3]

/-- Prime squares times a different prime and squarefree triples cannot share the two
arithmetic-function defects across a gap of twelve. Both orientations are covered. -/
theorem no_mixed_triple_gap_twelve {p q r s t : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime) (ht : t.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hgap : p ^ 2 * q + 12 = r * s * t ∨ r * s * t + 12 = p ^ 2 * q)
    (hφ : (p ^ 2 * q).totient + r * s * t = (r * s * t).totient + p ^ 2 * q)
    (hσ : σ 1 (p ^ 2 * q) + r * s * t = σ 1 (r * s * t) + p ^ 2 * q) : False := by
  have hc₁ := (Nat.coprime_primes hr hs).mpr hrs
  have hc₂ := ((Nat.coprime_primes hr ht).mpr hrt).mul_left
    ((Nat.coprime_primes hs ht).mpr hst)
  have hc₃ := ((Nat.coprime_primes hp hq).mpr hpq).pow_left 2
  have hp2 := hp.two_le
  by_cases he : p = 2
  · subst p
    have hsq : Squarefree (r*s*t) :=
      Nat.squarefree_mul_iff.mpr ⟨hc₂, Nat.squarefree_mul_iff.mpr ⟨hc₁, hr.squarefree, hs.squarefree⟩,
        ht.squarefree⟩
    have hdiv : 2 * 2 ∣ r*s*t := by
      norm_num at hgap ⊢
      omega
    exact (Nat.squarefree_iff_prime_squarefree.mp hsq 2 Nat.prime_two) hdiv
  have hp3 : 3 ≤ p := by omega
  have hp4 : p ≠ 4 := fun h => (by decide : ¬Nat.Prime 4) (h ▸ hp)
  have hσp {u : ℕ} (hu : u.Prime) : σ 1 u = u + 1 := by
    simpa using sigma_one_apply_prime_pow (i := 1) hu
  have hσpp : σ 1 (p ^ 2) = 1 + p + p ^ 2 := by
    simp only [sigma_one_apply_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, zero_add]
  have hφpp : (p ^ 2).totient = p * (p - 1) := by
    simpa using (Nat.totient_prime_pow_succ hp 1)
  rw [Nat.totient_mul hc₂, Nat.totient_mul hc₁, Nat.totient_mul hc₃,
    hφpp, Nat.totient_prime hq, Nat.totient_prime hr, Nat.totient_prime hs,
    Nat.totient_prime ht] at hφ
  rw [isMultiplicative_sigma.map_mul_of_coprime hc₂,
    isMultiplicative_sigma.map_mul_of_coprime hc₁,
    isMultiplicative_sigma.map_mul_of_coprime hc₃, hσpp, hσp hq, hσp hr, hσp hs, hσp ht] at hσ
  have hN₁ := newton_one r s t
  have hN₂ := newton_two r s t
  have hg : p ^ 2 * q ≤ r * s * t + 12 := by omega
  have hp₁ := hp.pos
  have hq₁ := hq.pos
  have hr₁ := hr.pos
  have hs₁ := hs.pos
  have ht₁ := ht.pos
  zify [hp₁, hq₁, hr₁, hs₁, ht₁] at hφ hσ hN₁ hN₂ hg hp3 hp4
  have hsum : 2*((r:ℤ)+s+t) = 2*p+(q+1) := by nlinarith only [hφ, hσ]
  have htwo : (r:ℤ)*s+r*t+s*t = (2*p+1)*((r:ℤ)+s+t) - (p+1)^2 := by
    have hh := congrArg (fun x : ℤ => (2*p+1)*x) hsum
    nlinarith only [hφ, hσ, hsum, hh]
  exact inconsistent_symmetric_bounds p (q+1) (r+s+t) (r*s+r*t+s*t) (r*s*t)
    hp3 (by positivity) hsum htwo (by nlinarith only [hg]) hN₁ hN₂ hp4

end A056777MixedTriple

#print axioms A056777MixedTriple.no_mixed_triple_gap_twelve
