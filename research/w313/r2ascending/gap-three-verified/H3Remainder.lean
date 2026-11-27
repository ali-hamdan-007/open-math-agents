import GapTwoVerified
import GapThreeVerified

namespace OMA.GreenR2GapThree

open OMA.GreenR2GapTwo (ExpectedH3 Nonalternating)

/-- Alternating ray heights with normalized gap at least four. -/
def GapAtLeastFour : Prop :=
  ∀ (R : Finset ℕ) (i j : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*i.val + 2 ∈ R → 13*j.val + 3 ∈ R →
    i.val + 3 < j.val → i.val + j.val ≤ 12 → False

/-- Gaps one through three are covered in the literal H3 formulation of R2. -/
theorem h3_of_gap_at_least_four_and_nonalternating
    (wide : GapAtLeastFour) (nonAlt : Nonalternating) : ExpectedH3 := by
  apply OMA.GreenR2GapTwo.h3_of_wider_and_nonalternating _ nonAlt
  intro R i j hno hhit hi hj hk hl hgap hnorm
  by_cases hwide : i.val + 3 < j.val
  · exact wide R i j hno hhit hi hj hk hl hwide hnorm
  · have hthree : j.val = i.val + 3 := by omega
    let S (x : ℕ) : Prop := x ∈ R
    let : DecidablePred S := fun a => inferInstanceAs (Decidable (a ∈ R))
    have noTriple (x y z : ℕ) (hx : S x) (hy : S y) (hz : S z) (h : x+z=2*y) :
        x = z := hno x hx y hy z hz h
    exact gap_three S i.val (by omega) noTriple hhit hi
      (by rw [hthree] at hj; exact hj) hk (by rw [hthree] at hl; exact hl)

/-- The exact R2.H3 statement is equivalent to its two remaining obligations. -/
theorem h3_iff_gap_at_least_four_and_nonalternating :
    ExpectedH3 ↔ GapAtLeastFour ∧ Nonalternating := by
  constructor
  · intro h3
    constructor
    · intro R i j hno hhit hi hj hk hl hgap hnorm
      exact h3 R i j i j hno hhit hi hj hk hl (by omega) (by omega) (by omega)
    · intro R i j k l hno hhit hi hj hk hl hfirst hsecond hnorm _
      exact h3 R i j k l hno hhit hi hj hk hl hfirst hsecond hnorm
  · rintro ⟨wide, nonAlt⟩
    exact h3_of_gap_at_least_four_and_nonalternating wide nonAlt

end OMA.GreenR2GapThree

#print axioms OMA.GreenR2GapThree.h3_of_gap_at_least_four_and_nonalternating

#print axioms OMA.GreenR2GapThree.h3_iff_gap_at_least_four_and_nonalternating
