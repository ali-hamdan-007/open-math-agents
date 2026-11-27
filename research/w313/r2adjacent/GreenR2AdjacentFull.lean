import Green154EdgeSeed
import GreenR2Adjacent

namespace OMA.GreenR2Adjacent

/-- Specializing the two sign tests and the lexicographic normalization of
R2-H2 to adjacent alternating heights leaves exactly the six heights 0 through 5. -/
theorem normalized_adjacent_iff (h : Nat) :
    (2*h < (h+1)+(h+1) ∧ h+h < 2*(h+1) ∧
      ((h+1)+h < 12 ∨ ((h+1)+h = 12 ∧ h+(h+1) ≤ 12))) ↔ h ≤ 5 := by
  omega

/-- The edge quartet completes the adjacent-height progression family. -/
theorem forces_progression_complete (r : Nat → Bool) (h : Nat) (hhi : h ≤ 5)
    (red : ∀ x ∈ [13*h+1, 13*h+3, 13*h+13, 13*h+15], r x = false) :
    OMA.Green160NearWitness.Mono r := by
  by_cases hz : h = 0
  · subst h
    exact OMA.Green154Edge.shifted_forces_progression r 0 (by decide) (by simpa using red)
  · exact forces_progression r h (by omega) hhi red

/-- The conclusion of R2-H2 for all six normalized adjacent alternating tuples
(h+1,h,h+1,h), with 0 ≤ h ≤ 5. -/
theorem r2_h2_adjacent_heights_complete (R : Nat → Prop) [DecidablePred R] (h : Nat)
    (hhi : h ≤ 5)
    (noTriple : ∀ x y z, R x → R y → R z → x + z = 2 * y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, R (a + t.val*d))
    (ri : R (13*(h+1))) (rj : R (13*h+1))
    (rk : R (13*(h+1)+2)) (rl : R (13*h+3)) : False := by
  by_cases hz : h = 0
  · subst h
    have red : ∀ x ∈ [1,3,13,15], decide (¬ R x) = false := by
      intro x hx
      have hcases : x = 1 ∨ x = 3 ∨ x = 13 ∨ x = 15 := by simpa using hx
      rcases hcases with rfl | rfl | rfl | rfl
      · simpa using rj
      · simpa using rl
      · simpa using ri
      · simpa using rk
    obtain ⟨b,a,d,hd,hend,hm⟩ :=
      OMA.Green154Edge.shifted_forces_progression (fun x => decide (¬ R x)) 0 (by decide)
        (by simpa using red)
    cases b
    · have hr (t : Nat) (ht : t ≤ 2) : R (a+t*d) := by simpa using hm t (by simpa using ht)
      have he := noTriple a (a+d) (a+2*d) (by simpa using hr 0 (by decide))
        (by simpa using hr 1 (by decide)) (hr 2 (by decide)) (by omega)
      omega
    · have blue (t : Nat) (ht : t ≤ 12) : ¬ R (a+t*d) := by simpa using hm t (by simpa using ht)
      have hb : a+12*d < 160 := hend
      by_cases hd12 : d ≤ 12
      · obtain ⟨t,rt⟩ := hit a d hd hd12 hb
        exact blue t.val (by have := t.isLt; omega) rt
      · have de : d = 13 := by omega
        subst d
        have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
        rcases ha with rfl | rfl | rfl | rfl
        · exact blue 1 (by decide) (by simpa using ri)
        · exact blue 0 (by decide) (by simpa using rj)
        · exact blue 1 (by decide) (by simpa using rk)
        · exact blue 0 (by decide) (by simpa using rl)
  · exact r2_h2_adjacent_heights R h (by omega) hhi noTriple hit ri rj rk rl

end OMA.GreenR2Adjacent

#print axioms OMA.GreenR2Adjacent.normalized_adjacent_iff
#print axioms OMA.GreenR2Adjacent.forces_progression_complete
#print axioms OMA.GreenR2Adjacent.r2_h2_adjacent_heights_complete
