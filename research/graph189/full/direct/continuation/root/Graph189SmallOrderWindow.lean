import Graph189LastCliqueOrders
import Graph189AllHighOrders
import Graph189AllDegreePathGap
import Graph189ModerateEight

open SimpleGraph Finset
namespace Graph189SmallOrderWindow
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Any counterexample to the exact original conjecture lies in the bounded
order theorem of the paper, with minimum degree three and connectivity two or more. -/
theorem necessary (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (bad : ¬∃a b,∃p : G.Walk a b,p.IsHamiltonian) :
    let k := G.secondSmallestDegree
    let n := Fintype.card V
    7≤k ∧ k≤21 ∧ 4*k≤n+5 ∧ n≤5*k-5 ∧ 3≤G.minDegree ∧ 2≤G.vertexConnectivity := by
  classical
  have lo : 7≤G.secondSmallestDegree := by
    by_contra! lower
    by_cases two : G.secondSmallestDegree≤2
    · exact bad (Graph189LowDegreeResidual.traceable_low_degree hc cap two)
    by_cases three : G.secondSmallestDegree=3
    · exact bad (Graph189ThreeOriginal.traceable_three hc cap three)
    by_cases four : G.secondSmallestDegree=4
    · exact bad (Graph189FourOriginal.traceable_four hc cap four)
    by_cases five : G.secondSmallestDegree=5
    · exact bad (Graph189FiveOriginal.traceable_five hc cap five)
    exact bad (Graph189SixOriginal.traceable_six hc cap (by omega))
  have hi : G.secondSmallestDegree≤21 := by
    by_contra! h
    exact bad (Graph189AllHighOrders.traceable hc cap h)
  have order : 4*G.secondSmallestDegree≤Fintype.card V+5 := by
    by_contra! short
    exact bad (Graph189ModerateEight.original_below_four hc cap lo short)
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have uncut : ∀v : V,(G.induce {u : V | u≠v}).Connected := by
    intro v
    by_contra h
    exact bad (Graph189CutH1.cut_vertex_case G hc point (by omega) ⟨v,h⟩)
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  have min : 3≤G.minDegree := by
    by_contra! h
    obtain ⟨z,least⟩ := G.exists_minimal_degree_vertex
    have degree := Graph189CutSides.connectivity_le_degree (G:=G) z
    exact bad (Graph189DegreeTwoOriginal.traceable hc cap conn z (by omega) lo)
  have endOrder : Fintype.card V≤5*G.secondSmallestDegree-5 := by
    by_contra! large
    exact bad (Graph189LastCliqueOrders.traceable hc cap lo hi (by omega))
  exact ⟨lo,hi,order,endOrder,min,conn⟩

end Graph189SmallOrderWindow
#print axioms Graph189SmallOrderWindow.necessary
