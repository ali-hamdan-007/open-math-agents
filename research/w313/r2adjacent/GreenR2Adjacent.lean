import Green137Window27
import Green150Window14
import Green130R2Bridge

namespace OMA.GreenR2Adjacent

/-- All adjacent alternating heights away from the edge tuple force a progression. -/
theorem forces_progression (r : Nat → Bool) (h : Nat) (hlo : 1 ≤ h) (hhi : h ≤ 5)
    (red : ∀ x ∈ [13*h+1, 13*h+3, 13*h+13, 13*h+15], r x = false) :
    OMA.Green160NearWitness.Mono r := by
  by_cases he : h = 1
  · subst h
    exact OMA.Green150Window.Seed14.shifted_forces_progression r 0 (by decide) (by simpa using red)
  by_cases hm : h ≤ 3
  · have hlow : 27 ≤ 13*h+1 := by omega
    apply OMA.Green137Window.Seed27.shifted_forces_progression r (13*h+1-27) (by omega)
    intro x hx
    have hcases : x = 27 ∨ x = 29 ∨ x = 39 ∨ x = 41 := by simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show 13*h+1-27+27 = 13*h+1 by omega]
      exact red _ (by simp)
    · rw [show 13*h+1-27+29 = 13*h+3 by omega]
      exact red _ (by simp)
    · rw [show 13*h+1-27+39 = 13*h+13 by omega]
      exact red _ (by simp)
    · rw [show 13*h+1-27+41 = 13*h+15 by omega]
      exact red _ (by simp)
  · apply OMA.Green130Window.Seed64.four_red_range_forces_progression r (13*h+1)
      (by omega) (by omega)
    intro x hx
    have hcases : x = 13*h+1 ∨ x = 13*h+1+2 ∨ x = 13*h+1+12 ∨ x = 13*h+1+14 := by
      simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl <;> exact red _ (by simp <;> omega)

/-- The conclusion of R2-H2 for every normalized tuple of the form
(h+1,h,h+1,h) with 1 ≤ h ≤ 5. -/
theorem r2_h2_adjacent_heights (R : Nat → Prop) [DecidablePred R] (h : Nat)
    (hlo : 1 ≤ h) (hhi : h ≤ 5)
    (noTriple : ∀ x y z, R x → R y → R z → x + z = 2 * y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, R (a + t.val*d))
    (ri : R (13*(h+1))) (rj : R (13*h+1))
    (rk : R (13*(h+1)+2)) (rl : R (13*h+3)) : False := by
  have hred : ∀ x ∈ [13*h+1, 13*h+3, 13*h+13, 13*h+15], decide (¬ R x) = false := by
    intro x hx
    have hcases : x = 13*h+1 ∨ x = 13*h+3 ∨ x = 13*h+13 ∨ x = 13*h+15 := by
      simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl
    · simpa using rj
    · simpa using rl
    · simpa [Nat.mul_add] using ri
    · simpa [Nat.mul_add, Nat.add_assoc] using rk
  obtain ⟨b,a,d,hd,hend,hm⟩ := forces_progression (fun x => decide (¬ R x)) h hlo hhi hred
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
      · apply blue (h+1) (by omega)
        simpa [Nat.mul_comm] using ri
      · apply blue h (by omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rj
      · apply blue (h+1) (by omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rk
      · apply blue h (by omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rl

end OMA.GreenR2Adjacent

#print axioms OMA.GreenR2Adjacent.forces_progression
#print axioms OMA.GreenR2Adjacent.r2_h2_adjacent_heights
