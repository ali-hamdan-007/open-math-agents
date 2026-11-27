import Lean

/-!
# A 159-point coloring for the mixed van der Waerden number W(3,13)

Positions are numbered 0 through 158. A set bit is color 0.
The intersection of shifted masks records all starts of a progression
with the given color and common difference.
-/
namespace Green13Witness

def redMask : Nat := 0x1400808110682005024002c40410828100082401

def blueMask : Nat := (2^159 - 1) ^^^ redMask

def color (i : Nat) : Fin 2 := if redMask.testBit i then 0 else 1

def intersect (mask d : Nat) (terms : List Nat) : Nat :=
  terms.foldr (fun t m => (mask >>> (t*d)) &&& m) (2^159 - 1)

theorem intersect_sound (mask a d : Nat) (terms : List Nat)
    (initial : (2^159 - 1 : Nat).testBit a = true)
    (h : ∀ t ∈ terms, mask.testBit (a+t*d) = true) :
    (intersect mask d terms).testBit a = true := by
  induction terms with
  | nil => exact initial
  | cons t ts ih =>
    change ((mask >>> (t*d)) &&& intersect mask d ts).testBit a = true
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_comm (t*d)]
    simp [h t (by simp), ih (fun u hu => h u (by simp [hu]))]

theorem bounds : ∀ a : Fin 159, (2^159 - 1 : Nat).testBit a.val = true := by decide +kernel

theorem checkRed : ∀ d : Fin 80, 0 < d.val →
    intersect redMask d.val (List.range 3) = 0 := by decide +kernel

theorem checkBlue : ∀ d : Fin 14, 0 < d.val →
    intersect blueMask d.val (List.range 13) = 0 := by decide +kernel

theorem no_red (a d : Nat) (hd : 0 < d) (hend : a + 2*d < 159) :
    ¬ ∀ i : Fin 3, color (a + i.val*d) = 0 := by
  intro h
  have hbit (t : Nat) (ht : t ∈ List.range 3) : redMask.testBit (a+t*d) = true := by
    have hh := h ⟨t,List.mem_range.mp ht⟩
    simpa [color] using hh
  have hh := intersect_sound redMask a d (List.range 3) (bounds ⟨a,by omega⟩) hbit
  have he := checkRed ⟨d,by omega⟩ hd
  change intersect redMask d (List.range 3) = 0 at he
  simp [he] at hh

theorem no_blue (a d : Nat) (hd : 0 < d) (hend : a + 12*d < 159) :
    ¬ ∀ i : Fin 13, color (a + i.val*d) = 1 := by
  intro h
  have hbit (t : Nat) (ht : t ∈ List.range 13) : blueMask.testBit (a+t*d) = true := by
    have ht' := List.mem_range.mp ht
    have hle := Nat.mul_le_mul_right d (show t ≤ 12 by omega)
    have hb := bounds ⟨a+t*d,by omega⟩
    have hh : redMask.testBit (a+t*d) = false := by simpa [color] using h ⟨t,ht'⟩
    simp [blueMask, Nat.testBit_xor, hh, hb]
  have hh := intersect_sound blueMask a d (List.range 13) (bounds ⟨a,by omega⟩) hbit
  have he := checkBlue ⟨d,by omega⟩ hd
  change intersect blueMask d (List.range 13) = 0 at he
  simp [he] at hh

end Green13Witness

#print axioms Green13Witness.no_red
#print axioms Green13Witness.no_blue
