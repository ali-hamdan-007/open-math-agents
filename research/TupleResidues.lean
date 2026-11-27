import Lean

namespace TupleResidues

-- Test membership among the square residues modulo 168.
private def squareResidue (v : Nat) : Bool :=
  (List.range 168).any fun k => (k * k) % 168 == v

private theorem residue_of_square (x : Nat) : squareResidue ((x * x) % 168) = true := by
  apply List.any_eq_true.mpr
  refine ⟨x % 168, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  exact beq_iff_eq.mpr (Nat.mul_mod x x 168).symm

-- This finite table checks every residue class. Each root is already reduced modulo 168.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem allowed : ∀ r : Fin 168,
    squareResidue ((r.val + 1) % 168) = true →
    squareResidue ((3 * r.val + 1) % 168) = true →
    squareResidue ((8 * r.val + 1) % 168) = true →
    r.val = 0 ∨ r.val = 120 := by decide

theorem necessary_residues (d x y z : Nat)
    (hx : d + 1 = x * x) (hy : 3 * d + 1 = y * y) (hz : 8 * d + 1 = z * z) :
    d % 168 = 0 ∨ d % 168 = 120 := by
  apply allowed ⟨d % 168, Nat.mod_lt _ (by decide)⟩
  · change squareResidue ((d % 168 + 1) % 168) = true
    rw [Nat.mod_add_mod, hx]
    exact residue_of_square x
  · change squareResidue ((3 * (d % 168) + 1) % 168) = true
    have he : (3 * (d % 168) + 1) % 168 = (3 * d + 1) % 168 := by omega
    rw [he, hy]
    exact residue_of_square y
  · change squareResidue ((8 * (d % 168) + 1) % 168) = true
    have he : (8 * (d % 168) + 1) % 168 = (8 * d + 1) % 168 := by omega
    rw [he, hz]
    exact residue_of_square z

end TupleResidues
