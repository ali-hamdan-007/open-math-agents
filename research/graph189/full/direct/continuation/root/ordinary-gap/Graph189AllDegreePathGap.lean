import Graph189OrdinaryNearOriginal
import Graph189LowDegreeOriginal
import Graph189ThreeOriginal
import Graph189FourOriginal
import Graph189FiveOriginal
import Graph189SixOriginal
import Graph189DegreeTwoOriginal
import Graph189ParentConnectivity

open SimpleGraph Finset
namespace Graph189OrdinaryPathGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The almost-spanning path implication in the separator paper under the
original assumptions, including cut vertices and the unique low vertex. -/
theorem traceable_of_near (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    {x y : V} (p : G.Walk x y) (hp : p.IsPath) (near : Near p) :
    ∃ a b : V, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  by_cases tiny : G.secondSmallestDegree≤2
  · exact Graph189LowDegreeResidual.traceable_low_degree hc cap tiny
  by_cases three : G.secondSmallestDegree=3
  · exact Graph189ThreeOriginal.traceable_three hc cap three
  by_cases four : G.secondSmallestDegree=4
  · exact Graph189FourOriginal.traceable_four hc cap four
  by_cases five : G.secondSmallestDegree=5
  · exact Graph189FiveOriginal.traceable_five hc cap five
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases minimum : 3≤G.minDegree
  · exact traceable_of_near_unrestricted hc point (by omega) minimum p hp near
  by_cases six : G.secondSmallestDegree=6
  · exact Graph189SixOriginal.traceable_six hc cap six
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases uncut : ∀ z : V, (G.induce {v : V | v≠z}).Connected
  swap
  · push Not at uncut
    exact Graph189CutH1.cut_vertex_case G hc point (by omega) uncut
  obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
  have two := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  have bound := Graph189CutSides.connectivity_le_degree (G:=G) z
  exact Graph189DegreeTwoOriginal.traceable hc cap two z (by omega) (by omega)

#print axioms traceable_of_near
end Graph189OrdinaryPathGap
