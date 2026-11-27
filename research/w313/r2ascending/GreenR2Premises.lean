import Green160NearWitness

namespace OMA.GreenR2Premises

open OMA.Green160NearWitness (Mono)

def rayPoints (i j k l : Fin 13) : List Nat :=
  [13*i.val, 13*j.val+1, 13*k.val+2, 13*l.val+3]

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

end OMA.GreenR2Premises

#print axioms OMA.GreenR2Premises.impossible_of_mono
