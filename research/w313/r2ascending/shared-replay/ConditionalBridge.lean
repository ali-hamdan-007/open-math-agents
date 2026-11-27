import ConditionalWindow
import H3CentralGapFour

namespace OMA.GreenR2GapFour

open OMA.GreenR2GapTwo (Nonalternating)

/-- The single width-147 window excludes normalized gap-four heights one and two. -/
theorem gap_four_shared
    (certificate : OMA.Green147GapThreeCore.Bad ([68,66,15,13],0x7fffff55fffffffffffb6fffffffffffdb7ff)) (R : Nat → Prop) [DecidablePred R]
    (h : Nat) (hlo : 1 ≤ h) (hhi : h ≤ 2)
    (noTriple : ∀ x y z, R x → R y → R z → x+z=2*y → x=z)
    (hit : ∀ a d : Nat, 0<d → d≤12 → a+12*d<160 → ∃ t : Fin 13, R (a+t.val*d))
    (ri : R (13*h)) (rj : R (13*(h+4)+1))
    (rk : R (13*h+2)) (rl : R (13*(h+4)+3)) : False := by
  let i : Fin 13 := ⟨h, by omega⟩
  let j : Fin 13 := ⟨h+4, by omega⟩
  apply OMA.GreenR2Premises.impossible_of_mono R i j i j noTriple hit
  · intro x hx
    have e : x = 13*h ∨ x = 13*(h+4)+1 ∨ x = 13*h+2 ∨ x = 13*(h+4)+3 := by
      simpa [OMA.GreenR2Premises.rayPoints, i, j] using hx
    rcases e with rfl | rfl | rfl | rfl
    · exact ri
    · exact rj
    · exact rk
    · exact rl
  · apply OMA.Green147GapThreeCore.GapFour13.shifted_forces_progression certificate _ (13*h-13) (by omega)
    intro x hx
    have e : x = 13 ∨ x = 15 ∨ x = 66 ∨ x = 68 := by simpa using hx
    rcases e with rfl | rfl | rfl | rfl
    · rw [show 13*h-13+13 = 13*h by omega]
      simp [ri]
    · rw [show 13*h-13+15 = 13*h+2 by omega]
      simp [rk]
    · rw [show 13*h-13+66 = 13*(h+4)+1 by omega]
      simp [rj]
    · rw [show 13*h-13+68 = 13*(h+4)+3 by omega]
      simp [rl]

/-- The gap-four endpoint and all alternating patterns with gap at least five. -/
def EndpointOrGapAtLeastFive : Prop :=
  ∀ (R : Finset ℕ) (i j : Fin 13),
    (∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, x + z = 2*y → x = z) →
    (∀ a d : ℕ, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, a + t.val*d ∈ R) →
    13*i.val ∈ R → 13*j.val + 1 ∈ R → 13*i.val + 2 ∈ R → 13*j.val + 3 ∈ R →
    i.val + 3 < j.val → i.val + j.val ≤ 12 → (i.val = 0 ∨ i.val + 4 < j.val) → False

theorem h3_iff_endpoint_or_gap_at_least_five_and_nonalternating
    (certificate : OMA.Green147GapThreeCore.Bad ([68,66,15,13],0x7fffff55fffffffffffb6fffffffffffdb7ff)) :
    OMA.R_Green14_W_3_13_R2.H3 ↔ EndpointOrGapAtLeastFive ∧ Nonalternating := by
  rw [h3_iff_alternating_remainder_and_nonalternating]
  constructor
  · rintro ⟨wide, nonAlt⟩
    refine ⟨?_, nonAlt⟩
    intro R i j hno hhit hi hj hk hl hgap hnorm hbranch
    exact wide R i j hno hhit hi hj hk hl hgap hnorm (by omega)
  · rintro ⟨remaining, nonAlt⟩
    refine ⟨?_, nonAlt⟩
    intro R i j hno hhit hi hj hk hl hgap hnorm hbranch
    by_cases hremaining : i.val = 0 ∨ i.val + 4 < j.val
    · exact remaining R i j hno hhit hi hj hk hl hgap hnorm hremaining
    · have hfour : j.val = i.val + 4 := by omega
      let S (x : ℕ) : Prop := x ∈ R
      let : DecidablePred S := fun a => inferInstanceAs (Decidable (a ∈ R))
      have noTriple (x y z : ℕ) (hx : S x) (hy : S y) (hz : S z) (h : x+z=2*y) :
          x = z := hno x hx y hy z hz h
      exact gap_four_shared certificate S i.val (by omega) (by omega) noTriple hhit hi
        (by rw [hfour] at hj; exact hj) hk (by rw [hfour] at hl; exact hl)

end OMA.GreenR2GapFour

#print axioms OMA.GreenR2GapFour.gap_four_shared
#print axioms OMA.GreenR2GapFour.h3_iff_endpoint_or_gap_at_least_five_and_nonalternating
