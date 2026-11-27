import Green147GapThreeCore
import Green160NearWitness

namespace OMA.Green147GapThreeCore.GapFour13

private def seedMask : List Nat → Nat
  | [] => 2 ^ 147 - 1
  | p :: ps => pvAfter ps (seedMask ps) p

private theorem seedMask_safe {r : Nat → Bool} (hn : ¬ Mono r)
    (ps : List Nat) (hs : ∀ p ∈ ps, Red r p) (x : Nat) (hx : Red r x) :
    (seedMask ps).testBit x = true := by
  induction ps with
  | nil =>
    have full : ∀ i : Fin 147, (2 ^ 147 - 1 : Nat).testBit i.val = true := by
      decide +kernel
    exact full ⟨x, hx.1⟩
  | cons p ps ih =>
    have hp : Red r p := hs p (by simp)
    have hps : ∀ q ∈ ps, Red r q := fun q hq => hs q (by simp [hq])
    exact pv_safe (noTriple hn) hps (fun _ hq => hq.1) hp hx (ih hps)

/-- The checked 147-point coloring branch. -/
theorem window_forces_progression
    (v1034 : Bad ([68,66,15,13],0x7fffff55fffffffffffb6fffffffffffdb7ff)) (r : Nat → Bool)
    (red : ∀ x ∈ [13, 15, 66, 68], r x = false) : Mono r := by
  apply Classical.byContradiction
  intro hn
  have known : ∀ x ∈ [68, 66, 15, 13], Red r x := by
    intro x hx
    have hcases : x = 68 ∨ x = 66 ∨ x = 15 ∨ x = 13 := by simpa using hx
    rcases hcases with rfl | rfl | rfl | rfl <;> exact ⟨by decide, red _ (by decide)⟩
  apply v1034 (Red r) (noTriple hn) (hits hn) (fun _ h => h.1) known
  have he : seedMask [68, 66, 15, 13] = 0x7fffff55fffffffffffb6fffffffffffdb7ff := by decide +kernel
  rw [← he]
  exact fun x hx => seedMask_safe hn _ known x hx

/-- A translated 147-point window fits in the 160-point interval for offsets 0 through 13. -/
theorem shifted_forces_progression
    (v1034 : Bad ([68,66,15,13],0x7fffff55fffffffffffb6fffffffffffdb7ff)) (r : Nat → Bool) (s : Nat) (hs : s ≤ 13)
    (red : ∀ x ∈ [13, 15, 66, 68], r (s + x) = false) : OMA.Green160NearWitness.Mono r := by
  obtain ⟨b,a,d,hd,hend,hmono⟩ := window_forces_progression v1034 (fun i => r (s+i)) red
  refine ⟨b,s+a,d,hd,?_,?_⟩
  · omega
  · intro t ht
    simpa only [Nat.add_assoc] using hmono t ht

/-- Reflecting the translated windows gives a second family of forbidden red sets. -/
theorem reflected_shifted_forces_progression
    (v1034 : Bad ([68,66,15,13],0x7fffff55fffffffffffb6fffffffffffdb7ff)) (r : Nat → Bool) (s : Nat) (hs : s ≤ 13)
    (red : ∀ x ∈ [13, 15, 66, 68], r (159 - (s + x)) = false) :
    OMA.Green160NearWitness.Mono r :=
  OMA.Green160NearWitness.reflect_progression r
    (shifted_forces_progression v1034 (fun i => r (159 - i)) s hs red)

end OMA.Green147GapThreeCore.GapFour13

#print axioms OMA.Green147GapThreeCore.GapFour13.shifted_forces_progression
#print axioms OMA.Green147GapThreeCore.GapFour13.reflected_shifted_forces_progression
