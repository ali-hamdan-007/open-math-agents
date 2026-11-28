import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace Graph189MatchedPack

/-- Signed contribution of one matching size to the wedge order bound. -/
def score (k t : ℕ) : ℤ := (t : ℤ) * ((k : ℤ) - t - 1)

/-- Sum of the two contributions when the capacity is divided as evenly as possible. -/
def packed (k capacity : ℕ) : ℤ :=
  score k (capacity / 2) + score k (capacity - capacity / 2)

/-- Equalizing the two integer sizes, and using the entire capacity, dominates the
contributions of the actual sizes and their remaining exceptional vertices. -/
theorem le_packed {k K t₁ t₂ ε₁ ε₂ : ℕ} (hK : K + 3 ≤ k)
    (hsize : t₁ + t₂ + ε₁ + ε₂ ≤ K) :
    score k t₁ + score k t₂ + ε₁ + ε₂ ≤ packed k K := by
  let a := K / 2
  let b := K - a
  change score k t₁ + score k t₂ + ε₁ + ε₂ ≤ score k a + score k b
  have hab : a + b = K := by dsimp [a,b]; omega
  have hab' : a = b ∨ b = a + 1 := by dsimp [a,b]; omega
  have habI : (a : ℤ) + b = (K : ℤ) := by exact_mod_cast hab
  have hsq : ((a : ℤ) - b)^2 ≤ 1 := by
    rcases hab' with h | h
    · have ha : (a : ℤ) = (b : ℤ) := by exact_mod_cast h
      rw [ha,sub_self]
      norm_num
    · have hd : (a : ℤ) - b = -1 := by omega
      rw [hd]
      norm_num
  have hid : 2 * (score k a + score k b - score k t₁ - score k t₂) =
      ((K : ℤ) - (t₁ + t₂ : ℤ)) * (2 * ((k : ℤ) - 1) - K - (t₁ + t₂ : ℤ)) +
      ((t₁ : ℤ) - t₂)^2 - ((a : ℤ) - b)^2 := by
    rw [← habI]
    unfold score
    ring
  by_cases heq : t₁ + t₂ = K
  · have hzero : (K : ℤ) - (t₁ + t₂ : ℤ) = 0 := by omega
    have hε₁ : ε₁ = 0 := by omega
    have hε₂ : ε₂ = 0 := by omega
    have hsmall : ((a : ℤ) - b)^2 ≤ ((t₁ : ℤ) - t₂)^2 := by
      rcases hab' with h | h
      · have ha : (a : ℤ) = (b : ℤ) := by exact_mod_cast h
        rw [ha,sub_self,zero_pow (by decide : 2 ≠ 0)]
        exact sq_nonneg _
      · have hne : t₁ ≠ t₂ := by omega
        have hlarge : 1 ≤ ((t₁ : ℤ) - t₂)^2 := by
          rcases lt_or_gt_of_ne hne with hh | hh
          · have hmult := mul_nonneg
              (show 0 ≤ (t₂ : ℤ) - t₁ - 1 by omega)
              (show 0 ≤ (t₂ : ℤ) - t₁ + 1 by omega)
            nlinarith only [hmult]
          · have hmult := mul_nonneg
              (show 0 ≤ (t₁ : ℤ) - t₂ - 1 by omega)
              (show 0 ≤ (t₁ : ℤ) - t₂ + 1 by omega)
            nlinarith only [hmult]
        exact hsq.trans hlarge
    rw [hzero,zero_mul,zero_add] at hid
    rw [hε₁,hε₂]
    simp only [Nat.cast_zero, add_zero]
    linarith only [hid,hsmall]
  · have hgap : 1 ≤ (K : ℤ) - (t₁ + t₂ : ℤ) := by omega
    have hfactor : 4 ≤ 2 * ((k : ℤ) - 1) - K - (t₁ + t₂ : ℤ) := by omega
    have hε : (ε₁ : ℤ) + ε₂ ≤ (K : ℤ) - (t₁ + t₂ : ℤ) := by omega
    have hprod := mul_nonneg (show 0 ≤ (K : ℤ) - (t₁ + t₂ : ℤ) by omega)
      (sub_nonneg.mpr hfactor)
    nlinarith only [hid,hgap,hε,hprod,hsq,sq_nonneg ((t₁ : ℤ) - t₂)]

#print axioms le_packed
end Graph189MatchedPack
