import Graph189UpstreamShortOrder
import Graph189LayerCutoff

open Finset SimpleGraph
namespace Graph189FiveShortOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The registered hypotheses at degree five with a degree-two vertex.
The local order ceiling fits the whole short-order theorem of @carl2sheriff. -/
theorem traceable_two (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (k5 : G.secondSmallestDegree=5) (z : V) (degree : G.degree z=2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using upper v
  have order := Graph189LayerCutoff.order_of_small_degree G hc z _ point (by omega)
  rw [degree,k5] at order
  by_cases small : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc upper small
  by_cases uncut : ∀ c : V, (G.induce {v : V | v≠c}).Connected
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R2.thm_D_all
      hc uncut upper (by omega) (by omega)
  push Not at uncut
  exact Graph189CutH1.cut_vertex_case G hc upper (by omega) uncut

#print axioms traceable_two
end Graph189FiveShortOrder
