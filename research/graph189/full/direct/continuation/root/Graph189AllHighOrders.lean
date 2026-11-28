import Graph189ParentFocused
import Graph189TwoConnectivity
import Graph189ThreeConnectivity
import Graph189FourConnectivityJoint
import Graph189LargeDegreeTrace
import Graph189ParentConnectivity

open Finset SimpleGraph
namespace Graph189AllHighOrders
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At most four connectivity values have to be distinguished. Every graph and
every order satisfying the original assumptions is included once k is at least 33. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 33≤G.secondSmallestDegree) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  classical
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  by_cases short : Fintype.card V≤2*G.secondSmallestDegree+2
  · exact OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2.theorem_C hc point short
  by_cases connected : ∀ c : V,(G.induce {v : V | v≠c}).Connected
  swap
  · push_neg at connected
    exact Graph189CutH1.cut_vertex_case G hc point (by omega) connected
  have two := Graph189ParentConnectivity.two_of_deletions hc (by omega) connected
  by_cases five : 5≤G.vertexConnectivity
  · exact Graph189LargeDegree.traceable hc cap (by omega) five
  by_cases four : G.vertexConnectivity=4
  · exact Graph189FourCut.traceable_of_33 hc cap four large
  by_cases three : G.vertexConnectivity=3
  · exact Graph189ThreeConnectivity.traceable_ge33 hc cap (by omega) three
  exact Graph189TwoConnectivity.traceable hc cap (by omega) (by omega)

end Graph189AllHighOrders
#print axioms Graph189AllHighOrders.traceable
