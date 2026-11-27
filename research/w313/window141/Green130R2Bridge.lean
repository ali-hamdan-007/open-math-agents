import Green130Window64

namespace OMA.Green130Window.Seed64

/-- The symmetric four-red shape is excluded at each start from 51 through 94. -/
theorem four_red_range_forces_progression (r : Nat → Bool) (a : Nat)
    (ha : 51 ≤ a) (hb : a ≤ 94)
    (red : ∀ x ∈ [a, a+2, a+12, a+14], r x = false) :
    OMA.Green160NearWitness.Mono r := by
  by_cases h : 64 ≤ a
  · apply shifted_forces_progression r (a-64) (by omega)
    intro x hx
    have hcases : x = 64 ∨ x = 66 ∨ x = 76 ∨ x = 78 := by simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show a-64+64 = a by omega]
      exact red _ (by simp)
    · rw [show a-64+66 = a+2 by omega]
      exact red _ (by simp)
    · rw [show a-64+76 = a+12 by omega]
      exact red _ (by simp)
    · rw [show a-64+78 = a+14 by omega]
      exact red _ (by simp)
  · apply reflected_shifted_forces_progression r (81-a) (by omega)
    intro x hx
    have hcases : x = 64 ∨ x = 66 ∨ x = 76 ∨ x = 78 := by simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show 159-(81-a+64) = a+14 by omega]
      exact red _ (by simp)
    · rw [show 159-(81-a+66) = a+12 by omega]
      exact red _ (by simp)
    · rw [show 159-(81-a+76) = a+2 by omega]
      exact red _ (by simp)
    · rw [show 159-(81-a+78) = a by omega]
      exact red _ (by simp)

/-- Convert the R2 ray assumptions into the full 13-progression hitting
property needed by an upper-bound branch. -/
private theorem impossible_ray_quartet (R : Nat → Prop) [DecidablePred R]
    (i j k l : Fin 13)
    (noTriple : ∀ x y z, R x → R y → R z → x + z = 2 * y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, R (a + t.val*d))
    (ri : R (13*i.val)) (rj : R (13*j.val+1))
    (rk : R (13*k.val+2)) (rl : R (13*l.val+3))
    (mono : OMA.Green160NearWitness.Mono (fun x => decide (¬ R x))) : False := by
  obtain ⟨b,a,d,hd,hend,hm⟩ := mono
  cases b
  · have hr (t : Nat) (ht : t ≤ 2) : R (a+t*d) := by
      have hh := hm t (by simpa using ht)
      simpa using hh
    have he := noTriple a (a+d) (a+2*d) (by simpa using hr 0 (by decide))
      (by simpa using hr 1 (by decide)) (hr 2 (by decide)) (by omega)
    omega
  · have blue (t : Nat) (ht : t ≤ 12) : ¬ R (a+t*d) := by
      have hh := hm t (by simpa using ht)
      simpa using hh
    by_cases hd12 : d ≤ 12
    · have hb : a + 12*d < 160 := hend
      obtain ⟨t,rt⟩ := hit a d hd hd12 hb
      exact blue t.val (by have := t.isLt; omega) rt
    · have hb : a + 12*d < 160 := hend
      have de : d = 13 := by omega
      subst d
      have ha : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases ha with rfl | rfl | rfl | rfl
      · apply blue i.val (by have := i.isLt; omega)
        simpa [Nat.mul_comm] using ri
      · apply blue j.val (by have := j.isLt; omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rj
      · apply blue k.val (by have := k.isLt; omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rk
      · apply blue l.val (by have := l.isLt; omega)
        simpa [Nat.mul_comm, Nat.add_comm] using rl

/-- The normalized R2-H2 tuple with heights (6, 5, 6, 5) is impossible. -/
theorem r2_heights_6565 (R : Nat → Prop) [DecidablePred R]
    (noTriple : ∀ x y z, R x → R y → R z → x + z = 2 * y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, R (a + t.val*d))
    (r78 : R 78) (r66 : R 66) (r80 : R 80) (r68 : R 68) : False := by
  apply impossible_ray_quartet R 6 5 6 5 noTriple hit r78 r66 r80 r68
  apply shifted_forces_progression _ 2 (by decide)
  intro x hx
  have hcases : x = 64 ∨ x = 66 ∨ x = 76 ∨ x = 78 := by simpa using hx
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa using r66
  · simpa using r68
  · simpa using r78
  · simpa using r80

/-- The normalized R2-H2 tuple with heights (5, 4, 5, 4) is impossible. -/
theorem r2_heights_5454 (R : Nat → Prop) [DecidablePred R]
    (noTriple : ∀ x y z, R x → R y → R z → x + z = 2 * y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a + 12*d < 160 →
      ∃ t : Fin 13, R (a + t.val*d))
    (r65 : R 65) (r53 : R 53) (r67 : R 67) (r55 : R 55) : False := by
  apply impossible_ray_quartet R 5 4 5 4 noTriple hit r65 r53 r67 r55
  apply reflected_shifted_forces_progression _ 28 (by decide)
  intro x hx
  have hcases : x = 64 ∨ x = 66 ∨ x = 76 ∨ x = 78 := by simpa using hx
  rcases hcases with rfl | rfl | rfl | rfl
  · simpa using r67
  · simpa using r65
  · simpa using r55
  · simpa using r53

end OMA.Green130Window.Seed64

#print axioms OMA.Green130Window.Seed64.four_red_range_forces_progression
#print axioms OMA.Green130Window.Seed64.r2_heights_6565
#print axioms OMA.Green130Window.Seed64.r2_heights_5454
