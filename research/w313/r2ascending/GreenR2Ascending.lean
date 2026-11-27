import Green147Window52
import GreenR2Premises

namespace OMA.GreenR2Ascending

open OMA.Green160NearWitness (Mono)

def points (a : Nat) : List Nat := [a, a+2, a+14, a+16]

def RedShape (r : Nat → Bool) (a : Nat) : Prop := ∀ x ∈ points a, r x = false

private theorem forward_forces (r : Nat → Bool) (a : Nat) (ha : 52 ≤ a) (hb : a ≤ 65)
    (red : RedShape r a) : Mono r := by
  apply OMA.Green147Window.Seed52.shifted_forces_progression r (a-52) (by omega)
  intro x hx
  have hx' : x = 52 ∨ x = 54 ∨ x = 66 ∨ x = 68 := by simpa using hx
  rcases hx' with rfl | rfl | rfl | rfl
  · rw [show a-52+52 = a by omega]
    exact red _ (by simp [points])
  · rw [show a-52+54 = a+2 by omega]
    exact red _ (by simp [points])
  · rw [show a-52+66 = a+14 by omega]
    exact red _ (by simp [points])
  · rw [show a-52+68 = a+16 by omega]
    exact red _ (by simp [points])

/-- The ascending four-red shape forces a progression at any of 28 starts. -/
theorem forces_of_ascending_start (r : Nat → Bool) (a : Nat)
    (covered : (52 ≤ a ∧ a ≤ 65) ∨ (78 ≤ a ∧ a ≤ 91))
    (red : RedShape r a) : Mono r := by
  rcases covered with h | h
  · exact forward_forces r a h.1 h.2 red
  · apply OMA.Green160NearWitness.reflect_progression
    apply forward_forces (fun x => r (159-x)) (143-a) (by omega) (by omega)
    intro x hx
    have hx' : x = 143-a ∨ x = 143-a+2 ∨ x = 143-a+14 ∨ x = 143-a+16 := by
      simpa [points] using hx
    rcases hx' with rfl | rfl | rfl | rfl <;> dsimp only
    · rw [show 159-(143-a) = a+16 by omega]
      exact red _ (by simp [points])
    · rw [show 159-(143-a+2) = a+14 by omega]
      exact red _ (by simp [points])
    · rw [show 159-(143-a+14) = a+2 by omega]
      exact red _ (by simp [points])
    · rw [show 159-(143-a+16) = a by omega]
      exact red _ (by simp [points])

/-- The H3 signs and normalization permit exactly six adjacent ascending heights. -/
theorem normalized_ascending_iff (h : Nat) :
    (h+h < 2*(h+1) ∧ 2*h < (h+1)+(h+1) ∧
      (h+(h+1) < 12 ∨ (h+(h+1) = 12 ∧ (h+1)+h ≤ 12))) ↔ h ≤ 5 := by
  omega

/-- The conclusion of R2-H3 for adjacent ascending tuples (h,h+1,h,h+1)
at normalized heights 4 and 5. Heights 6 and 7 are their unnormalized reflections. -/
theorem r2_h3_ascending_heights (R : Nat → Prop) [DecidablePred R] (h : Nat)
    (hlo : 4 ≤ h) (hhi : h ≤ 7)
    (noTriple : ∀ x y z, R x → R y → R z → x+z = 2*y → x = z)
    (hit : ∀ a d : Nat, 0 < d → d ≤ 12 → a+12*d < 160 →
      ∃ t : Fin 13, R (a+t.val*d))
    (ri : R (13*h)) (rj : R (13*(h+1)+1))
    (rk : R (13*h+2)) (rl : R (13*(h+1)+3)) : False := by
  let u : Fin 13 := ⟨h, by omega⟩
  let v : Fin 13 := ⟨h+1, by omega⟩
  apply OMA.GreenR2Premises.impossible_of_mono R u v u v noTriple hit
  · intro x hx
    have hx' : x = 13*h ∨ x = 13*(h+1)+1 ∨ x = 13*h+2 ∨ x = 13*(h+1)+3 := by
      simpa [OMA.GreenR2Premises.rayPoints, u, v] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · exact ri
    · exact rj
    · exact rk
    · exact rl
  · apply forces_of_ascending_start _ (13*h) (by omega)
    intro x hx
    have hx' : x = 13*h ∨ x = 13*h+2 ∨ x = 13*h+14 ∨ x = 13*h+16 := by
      simpa [points] using hx
    rcases hx' with rfl | rfl | rfl | rfl
    · simpa using ri
    · simpa using rk
    · simpa [Nat.mul_add, Nat.add_assoc] using rj
    · simpa [Nat.mul_add, Nat.add_assoc] using rl

end OMA.GreenR2Ascending

#print axioms OMA.GreenR2Ascending.forces_of_ascending_start
#print axioms OMA.GreenR2Ascending.normalized_ascending_iff
#print axioms OMA.GreenR2Ascending.r2_h3_ascending_heights
