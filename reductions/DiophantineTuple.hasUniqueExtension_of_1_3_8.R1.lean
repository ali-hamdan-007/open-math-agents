import FormalConjectures.Wikipedia.DiophantineTuple
import Mathlib.Tactic.NormNum.IsSquare

namespace OMA.R_DiophantineTuple_hasUniqueExtension_of_1_3_8_R1

open DiophantineTuple

/-- The finite range of the simultaneous square conditions. -/
def H1 : Prop :=
  ∀ d : ℕ, d < 10 ^ 200 →
    IsSquare (d + 1) → IsSquare (3 * d + 1) → IsSquare (8 * d + 1) →
    d = 0 ∨ d = 120

/-- An upper bound for simultaneous solutions of the three square conditions. -/
def H2 : Prop :=
  ∀ d : ℕ, IsSquare (d + 1) → IsSquare (3 * d + 1) → IsSquare (8 * d + 1) →
    d < 10 ^ 200

theorem main : H1 → H2 → type_of% @DiophantineTuple.hasUniqueExtension_of_1_3_8 := by
  intro hfinite hbound
  refine ⟨?_, ?_⟩
  · norm_num [IsDiophantineTuple]
  · intro d ht hd
    have hlarge : 8 < d := by simpa using hd
    have hmem : d ∈ ({1, 3, 8, d} : Finset ℕ) := by simp
    have h₁ : IsSquare (d + 1) := by
      simpa only [one_mul] using ht.2 1 (by simp) d hmem (by omega)
    have h₃ : IsSquare (3 * d + 1) := ht.2 3 (by simp) d hmem (by omega)
    have h₈ : IsSquare (8 * d + 1) := ht.2 8 (by simp) d hmem (by omega)
    have hv : regularExtension 1 3 8 = 120 := by
      unfold regularExtension
      decide +kernel
    rw [hv]
    rcases hfinite d (hbound d h₁ h₃ h₈) h₁ h₃ h₈ with hzero | he
    · omega
    · exact he

end OMA.R_DiophantineTuple_hasUniqueExtension_of_1_3_8_R1
