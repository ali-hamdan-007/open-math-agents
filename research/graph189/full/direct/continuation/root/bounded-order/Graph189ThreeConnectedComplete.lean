import Graph189FanCircumference
import Graph189LongCycleAssembly
import Graph189SmallOrderWindow

open SimpleGraph Finset
namespace Graph189ExteriorLeaf

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The original even-distance condition implies a Hamiltonian path at
vertex connectivity at least three, with no bound on order or degree. -/
theorem traceable_three_connected (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (conn : 3 ≤ G.vertexConnectivity) : ∃ a b, ∃ Q : G.Walk a b, Q.IsHamiltonian := by
  classical
  by_contra bad
  obtain ⟨lo, hi, _, upper, minimum, _⟩ := Graph189SmallOrderWindow.necessary hc cap bad
  exact bad (three_connected_of_long_cycles hc cap lo hi upper minimum conn
    (Graph189FanCycle.induced_long_cycles G))

end Graph189ExteriorLeaf

#print axioms Graph189ExteriorLeaf.traceable_three_connected
