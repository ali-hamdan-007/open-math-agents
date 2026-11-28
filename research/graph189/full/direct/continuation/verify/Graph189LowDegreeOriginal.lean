import Graph189LowDegreeResidual
import Graph189ParentFocused

namespace Graph189LowDegreeResidual
open Finset SimpleGraph

/-- All original Graph 189 graphs with second-smallest degree at most two
admit a Hamiltonian path, regardless of their order, connectivity or diameter. -/
theorem traceable_low_degree {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hk : G.secondSmallestDegree ≤ 2) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have cap (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans hcap
  by_cases small : Fintype.card V ≤ 2*G.secondSmallestDegree + 2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc cap small
  by_cases uncut : ∀ z : V, (G.induce {v | v ≠ z}).Connected
  · exact low_degree_residual hc hcap uncut (by omega) hk
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc cap (by omega) uncut

#print axioms traceable_low_degree
end Graph189LowDegreeResidual
