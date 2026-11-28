import Graph189ModerateSeven
import Graph189SixOrder
import Graph189SixMinimumThree

open SimpleGraph Finset
namespace Graph189ModerateSix
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The full original conjecture at all moderate orders and second-smallest
degree at least six. -/
theorem original (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 6≤G.secondSmallestDegree) (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  by_cases seven : 7≤G.secondSmallestDegree
  · exact Graph189ModerateSeven.original hc cap seven order
  have six : G.secondSmallestDegree=6 := by omega
  have small : Fintype.card V≤20 := by omega
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have localCap (v : V) : G.distEven v≤G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using point v
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases survives : ∀ z : V, (G.induce {v | v≠z}).Connected
  · have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) survives
    obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
    have lower := Graph189CutSides.connectivity_le_degree (G:=G) z
    by_cases dz : G.degree z=2
    · exact Graph189SixOrder.traceable_degree_two hc cap six z dz
    exact Graph189SixMinimumThree.traceable conn six (by omega) small localCap
  push Not at survives
  exact Graph189CutH1.cut_vertex_case G hc point (by omega) survives

end Graph189ModerateSix
#print axioms Graph189ModerateSix.original
