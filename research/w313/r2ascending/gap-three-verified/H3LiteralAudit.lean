import H3Remainder

namespace OMA.R_Green14_W_3_13_R2

def H3 : Prop :=
  ∀ (R : Finset ℕ) (i j k l : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*k.val + 2 ∈ R → 13*l.val + 3 ∈ R →
    i.val + k.val < 2*j.val → 2*k.val < j.val + l.val →
    (i.val + l.val < 12 ∨ (i.val + l.val = 12 ∧ j.val + k.val ≤ 12)) → False

example : H3 = OMA.GreenR2GapTwo.ExpectedH3 := rfl

example : H3 ↔ OMA.GreenR2GapThree.GapAtLeastFour ∧ OMA.GreenR2GapTwo.Nonalternating :=
  OMA.GreenR2GapThree.h3_iff_gap_at_least_four_and_nonalternating

end OMA.R_Green14_W_3_13_R2
