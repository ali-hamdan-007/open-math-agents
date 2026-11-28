import Graph189SixAllConnected
import Graph189SixOrder
import Graph189ParentConnectivity

open Finset SimpleGraph
namespace Graph189SixOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact original conjecture at second-smallest degree six, for
all finite graphs and all orders. -/
theorem traceable_six (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) : ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases small : Fintype.card V≤19
  · exact Graph189SixOrder.traceable hc cap degree small
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases survives : ∀ c : V, (G.induce {v : V | v≠c}).Connected
  swap
  · push Not at survives
    exact Graph189CutH1.cut_vertex_case G hc point (by omega) survives
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) survives
  by_cases two : ∃z, G.degree z=2
  · obtain ⟨z,hz⟩ := two
    exact Graph189SixOrder.traceable_degree_two hc cap degree z hz
  have minimum (v : V) : 3≤G.degree v := by
    have h := Graph189CutSides.connectivity_le_degree (G:=G) v
    have ne : G.degree v≠2 := fun e => two ⟨v,e⟩
    omega
  exact Graph189SixAllConnected.traceable hc cap degree conn minimum

#print axioms traceable_six
end Graph189SixOriginal
