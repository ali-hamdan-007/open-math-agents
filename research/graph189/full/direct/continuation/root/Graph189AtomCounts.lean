import Mathlib.Data.Nat.Basic

namespace Graph189AtomCounts

/-- Mader's atom count in the three-by-three intersection array of two
minimum vertex cuts. The first cut side is an atom and the second cut
meets it. A positive corner on the atom row has boundary strictly larger
than a minimum cut. Positive corners on the opposite row have boundary
at least as large as a minimum cut. -/
theorem atom_count {ac atc ad sc st sd bc bt bd s a : ℕ}
    (size : a = ac+atc+ad) (row : s = sc+st+sd) (col : s = atc+st+bt)
    (cSize : a ≤ ac+sc+bc) (dSize : a ≤ ad+sd+bd)
    (cCorner : 0 < ac → s < atc+st+sc) (dCorner : 0 < ad → s < atc+st+sd)
    (cOpp : 0 < bc → s ≤ bt+st+sc) (dOpp : 0 < bd → s ≤ bt+st+sd) :
    ac = 0 ∧ ad = 0 ∧ 2*a ≤ s := by
  have first : ac = 0 := by
    by_cases pos : ac = 0
    · exact pos
    have split := cCorner (by omega)
    by_cases opposite : 0 < bd
    · have := dOpp opposite
      omega
    · omega
  have last : ad = 0 := by
    by_cases pos : ad = 0
    · exact pos
    have split := dCorner (by omega)
    by_cases opposite : 0 < bc
    · have := cOpp opposite
      omega
    · omega
  have c : a ≤ sc := by
    by_cases h : 0 < bc
    · have := cOpp h
      omega
    · omega
  have d : a ≤ sd := by
    by_cases h : 0 < bd
    · have := dOpp h
      omega
    · omega
  exact ⟨first,last,by omega⟩

#print axioms atom_count
end Graph189AtomCounts
