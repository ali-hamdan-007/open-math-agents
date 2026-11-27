import Lean

namespace OMA.GreenR2GapFour

/-- A translation that carries both outer rays into the four rays has step divisible by 13. -/
theorem ray_translation_mod (s x y : Nat)
    (hx : x % 13 = 0) (hy : y % 13 = 3)
    (hxs : (x+s) % 13 ≤ 3) (hys : (y+s) % 13 ≤ 3) :
    s % 13 = 0 := by
  rw [Nat.add_mod x s, hx, Nat.zero_add, Nat.mod_mod] at hxs
  rw [Nat.add_mod y s, hy, Nat.mod_eq_of_lt (by omega : 3 + s % 13 < 13)] at hys
  omega

/-- Number of normalized H3 choices for the inner rays when the outer rays
occupy the endpoints 0 and 159. All these tuples are nonalternating. -/
theorem endpoint_nonalternating_count :
    (((List.range 13).flatMap fun j => (List.range 13).map fun k => (j, k)).filter
      fun (j, k) => decide (k < 2*j ∧ 2*k < j+12 ∧ j+k ≤ 12 ∧ (k ≠ 0 ∨ j ≠ 12))).length = 55 := by
  decide +kernel

/-- No proper contiguous subwindow of the 160 sites contains both endpoints. -/
theorem endpoint_width (a w : Nat) (hfit : a+w ≤ 160)
    (hzero : a ≤ 0) (hlast : 159 < a+w) : w = 160 := by
  omega

end OMA.GreenR2GapFour

#print axioms OMA.GreenR2GapFour.ray_translation_mod
#print axioms OMA.GreenR2GapFour.endpoint_nonalternating_count
#print axioms OMA.GreenR2GapFour.endpoint_width
