import GreenR2AdjacentFull

namespace OMA.GreenR2SeedGeometry

open OMA.Green160NearWitness (Mono)

def points (a : Nat) : List Nat := [a, a+2, a+12, a+14]

def RedShape (r : Nat → Bool) (a : Nat) : Prop := ∀ x ∈ points a, r x = false

def Forward (a : Nat) : Prop :=
  (1 ≤ a ∧ a ≤ 7) ∨ (14 ≤ a ∧ a ≤ 24) ∨ (27 ≤ a ∧ a ≤ 50) ∨ (64 ≤ a ∧ a ≤ 94)

def Covered (a : Nat) : Prop := a ≤ 145 ∧ (Forward a ∨ Forward (145-a))

theorem covered_iff (a : Nat) : Covered a ↔
    (1 ≤ a ∧ a ≤ 7) ∨ (14 ≤ a ∧ a ≤ 24) ∨ (27 ≤ a ∧ a ≤ 118) ∨
    (121 ≤ a ∧ a ≤ 131) ∨ (138 ≤ a ∧ a ≤ 144) := by
  unfold Covered Forward
  omega

private theorem shift_condition (r : Nat → Bool) (w s : Nat)
    (red : RedShape r (s+w)) :
    ∀ x ∈ points w, r (s+x) = false := by
  intro x hx
  have hcases : x = w ∨ x = w+2 ∨ x = w+12 ∨ x = w+14 := by
    simpa [points] using hx
  rcases hcases with rfl | rfl | rfl | rfl
  · exact red _ (by simp [points])
  · rw [← Nat.add_assoc]
    exact red _ (by simp [points])
  · rw [← Nat.add_assoc]
    exact red _ (by simp [points])
  · rw [← Nat.add_assoc]
    exact red _ (by simp [points])

private theorem use_window (r : Nat → Bool) (a w m : Nat)
    (lo : w ≤ a) (hi : a ≤ w+m)
    (window : ∀ s ≤ m, (∀ x ∈ points w, r (s+x) = false) → Mono r)
    (red : RedShape r a) : Mono r := by
  apply window (a-w) (by omega)
  apply shift_condition
  simpa only [Nat.sub_add_cancel lo] using red

private theorem forward_forces (r : Nat → Bool) (a : Nat)
    (covered : Forward a) (red : RedShape r a) : Mono r := by
  rcases covered with h | h | h | h
  · exact use_window r a 1 6 h.1 h.2 (OMA.Green154Edge.shifted_forces_progression r) red
  · exact use_window r a 14 10 h.1 h.2 (OMA.Green150Window.Seed14.shifted_forces_progression r) red
  · exact use_window r a 27 23 h.1 h.2 (OMA.Green137Window.Seed27.shifted_forces_progression r) red
  · exact use_window r a 64 30 h.1 h.2 (OMA.Green130Window.Seed64.shifted_forces_progression r) red

private theorem reflect_condition (r : Nat → Bool) (a : Nat) (ha : a ≤ 145)
    (red : RedShape r a) :
    RedShape (fun x => r (159-x)) (145-a) := by
  intro x hx
  have hcases : x = 145-a ∨ x = 145-a+2 ∨ x = 145-a+12 ∨ x = 145-a+14 := by
    simpa [points] using hx
  rcases hcases with rfl | rfl | rfl | rfl
  · have h := red (a+14) (by simp [points])
    simpa only [show 159-(145-a) = a+14 by omega] using h
  · have h := red (a+12) (by simp [points])
    simpa only [show 159-(145-a+2) = a+12 by omega] using h
  · have h := red (a+2) (by simp [points])
    simpa only [show 159-(145-a+12) = a+2 by omega] using h
  · have h := red a (by simp [points])
    simpa only [show 159-(145-a+14) = a by omega] using h

/-- Every start covered by the original windows and their reflections is
certified with the same four-red implication. -/
theorem forces_of_covered (r : Nat → Bool) (a : Nat)
    (covered : Covered a) (red : RedShape r a) : Mono r := by
  obtain ⟨ha, h | h⟩ := covered
  · exact forward_forces r a h red
  · exact OMA.Green160NearWitness.reflect_progression r
      (forward_forces _ _ h (reflect_condition r a ha red))

def rayPoints (i j k l : Fin 13) : List Nat :=
  [13*i.val, 13*j.val+1, 13*k.val+2, 13*l.val+3]

private theorem residue_le_three {i j k l : Fin 13} {x : Nat}
    (hx : x ∈ rayPoints i j k l) : x % 13 ≤ 3 := by
  have hcases : x = 13*i.val ∨ x = 13*j.val+1 ∨ x = 13*k.val+2 ∨ x = 13*l.val+3 := by
    simpa [rayPoints] using hx
  omega

/-- A four-red translated shape fits the R2 rays exactly for the descending
adjacent alternation. This tests all unnormalized ray tuples as well. -/
theorem ray_shape_iff (i j k l : Fin 13) (a : Nat) :
    (∀ x ∈ points a, x ∈ rayPoints i j k l) ↔
    ∃ h ≤ 11, a = 13*h+1 ∧ i.val = h+1 ∧ j.val = h ∧ k.val = h+1 ∧ l.val = h := by
  constructor
  · intro incl
    have ha := incl a (by simp [points])
    have hb := incl (a+2) (by simp [points])
    have hc := incl (a+12) (by simp [points])
    have hd := incl (a+14) (by simp [points])
    have ha3 := residue_le_three ha
    have hb3 := residue_le_three hb
    have hc3 := residue_le_three hc
    have hamod : a % 13 = 1 := by omega
    let h := a / 13
    have hav : a = 13*h+1 := by dsimp [h]; omega
    have hj : j.val = h := by
      simp [rayPoints] at ha
      omega
    have hl : l.val = h := by
      simp [rayPoints] at hb
      omega
    have hi : i.val = h+1 := by
      simp [rayPoints] at hc
      omega
    have hk : k.val = h+1 := by
      simp [rayPoints] at hd
      omega
    exact ⟨h, by have := i.isLt; omega, hav, hi, hj, hk, hl⟩
  · rintro ⟨h, _, rfl, hi, hj, hk, hl⟩ x hx
    simp [points] at hx
    simp [rayPoints, hi, hj, hk, hl]
    omega

/-- The earlier non-symmetric seed shape never fits the four R2 rays.
Only its first two required red points are needed for this exclusion. -/
theorem other_shape_cannot_fit (i j k l : Fin 13) (a : Nat)
    (ha : a ∈ rayPoints i j k l) (hb : a+4 ∈ rayPoints i j k l) : False := by
  have := residue_le_three ha
  have := residue_le_three hb
  omega

/-- A reflected fit is a fit on the reflected rays. -/
theorem reflected_ray_mem (i j k l : Fin 13) (x : Nat)
    (hx : x ∈ rayPoints i j k l) :
    159-x ∈ rayPoints (Fin.rev l) (Fin.rev k) (Fin.rev j) (Fin.rev i) := by
  have hcases : x = 13*i.val ∨ x = 13*j.val+1 ∨ x = 13*k.val+2 ∨ x = 13*l.val+3 := by
    simpa [rayPoints] using hx
  have hi := i.isLt
  have hj := j.isLt
  have hk := k.isLt
  have hl := l.isLt
  simp [rayPoints, Fin.val_rev]
  omega

theorem covered_at_rays (h : Nat) (hh : h ≤ 11) : Covered (13*h+1) := by
  rw [covered_iff]
  omega

/-- A complete classifier for the symmetric certified shape in the R2 rays. -/
theorem covered_ray_shape_iff (i j k l : Fin 13) (a : Nat) :
    (Covered a ∧ ∀ x ∈ points a, x ∈ rayPoints i j k l) ↔
    ∃ h ≤ 11, a = 13*h+1 ∧ i.val = h+1 ∧ j.val = h ∧ k.val = h+1 ∧ l.val = h := by
  constructor
  · exact fun h => (ray_shape_iff _ _ _ _ _).mp h.2
  · intro h
    refine ⟨?_, (ray_shape_iff _ _ _ _ _).mpr h⟩
    obtain ⟨t, ht, rfl, _, _, _, _⟩ := h
    exact covered_at_rays t ht

/-- Reflection preserves the direction of an alternating pair of heights. -/
theorem reflection_preserves_orientation (i j : Fin 13) :
    (Fin.rev j).val < (Fin.rev i).val ↔ i.val < j.val := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Fin.val_rev]
  omega

theorem ascending_cannot_fit (i j : Fin 13) (a : Nat) (h : i.val < j.val) :
    ¬ (∀ x ∈ points a, x ∈ rayPoints i j i j) := by
  intro incl
  obtain ⟨t, _, _, hi, hj, _, _⟩ := (ray_shape_iff i j i j a).mp incl
  omega

theorem reflected_other_shape_cannot_fit (i j k l : Fin 13) (a : Nat)
    (ha : a+4 ≤ 159)
    (h₁ : 159-a ∈ rayPoints i j k l) (h₂ : 159-(a+4) ∈ rayPoints i j k l) : False := by
  have h₁' := reflected_ray_mem i j k l _ h₁
  have h₂' := reflected_ray_mem i j k l _ h₂
  rw [show 159-(159-a) = a by omega] at h₁'
  rw [show 159-(159-(a+4)) = a+4 by omega] at h₂'
  exact other_shape_cannot_fit _ _ _ _ _ h₁' h₂'

/-- The R2 premises forbid any monochromatic progression of the target lengths.
The four ray witnesses supply precisely the missing step-13 hitting cases. -/
theorem impossible_of_mono (R : Nat → Prop) [DecidablePred R] (i j k l : Fin 13)
    (noTriple : ∀ x y z, R x → R y → R z → x+z = 2*y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a+12*d < 160 →
      ∃ t : Fin 13, R (a+t.val*d))
    (ray : ∀ x ∈ rayPoints i j k l, R x)
    (mono : Mono (fun x => decide (¬ R x))) : False := by
  obtain ⟨b,a,d,hd,hend,hm⟩ := mono
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
      · apply blue i.val (by have := i.isLt; omega)
        apply ray
        simp [rayPoints, Nat.mul_comm]
      · apply blue j.val (by have := j.isLt; omega)
        apply ray
        simp [rayPoints, Nat.mul_comm, Nat.add_comm]
      · apply blue k.val (by have := k.isLt; omega)
        apply ray
        simp [rayPoints, Nat.mul_comm, Nat.add_comm]
      · apply blue l.val (by have := l.isLt; omega)
        apply ray
        simp [rayPoints, Nat.mul_comm, Nat.add_comm]

/-- Apply the existing proof windows to the R2 premises using one coverage
fact and one inclusion of checked red points. -/
theorem r2_of_covered_shape (R : Nat → Prop) [DecidablePred R] (i j k l : Fin 13) (a : Nat)
    (noTriple : ∀ x y z, R x → R y → R z → x+z = 2*y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a+12*d < 160 →
      ∃ t : Fin 13, R (a+t.val*d))
    (ray : ∀ x ∈ rayPoints i j k l, R x)
    (covered : Covered a) (incl : ∀ x ∈ points a, x ∈ rayPoints i j k l) : False := by
  apply impossible_of_mono R i j k l noTriple hit ray
  apply forces_of_covered _ a covered
  intro x hx
  simpa using ray x (incl x hx)

end OMA.GreenR2SeedGeometry

#print axioms OMA.GreenR2SeedGeometry.forces_of_covered
#print axioms OMA.GreenR2SeedGeometry.covered_ray_shape_iff
#print axioms OMA.GreenR2SeedGeometry.reflected_ray_mem
#print axioms OMA.GreenR2SeedGeometry.r2_of_covered_shape
