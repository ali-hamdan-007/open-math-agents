import Graph189FiveHighMinimum
import Graph189FiveShortOrder

open SimpleGraph Finset
namespace Graph189FiveOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact registered conjecture holds whenever the second entry of the
nondecreasing degree sequence equals five. -/
theorem traceable_five (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (k5 : G.secondSmallestDegree=5) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases minimum : 3 ≤ G.minDegree
  · exact Graph189FiveHighMinimum.traceable hc cap k5 minimum
  have localCap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V ≤ 2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc localCap short
  obtain ⟨z,eq⟩ := G.exists_minimal_degree_vertex
  have two := Graph189CutBounds.two_le_degree hc localCap (by omega) z
  exact Graph189FiveShortOrder.traceable_two hc cap k5 z (by omega)

#print axioms traceable_five
end Graph189FiveOriginal
