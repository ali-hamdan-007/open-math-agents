import Graph189ExcludeValid
import Graph189SyntheticBand

open Finset SimpleGraph
namespace Graph189GlobalOrder

/-- Both universal upper-order inputs of the unbounded numerical proof
follow from the same separator contradiction on an explicitly valid band. -/
theorem upper_orders {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hc : G.Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected) :
    let s : ℤ := G.vertexConnectivity
    let k : ℤ := G.secondSmallestDegree
    let n : ℤ := Fintype.card V
    5≤s → 6*(s-1)<k → 2*n<(2*s+3)*k+4*s+4 ∧
      (s-2)*(n-2*s-3)<((s+1)*(s-2)+3)*k := by
  intro s k n hs hk
  by_contra bad
  have branch : (2*s+3)*k+4*s+4≤2*n ∨ ((s+1)*(s-2)+3)*k≤(s-2)*(n-2*s-3) := by omega
  have row := Graph189SyntheticBand.high_order hs hk branch
  exact Graph189ExcludeValid.impossible hc cap deletion row rfl rfl le_rfl

#print axioms upper_orders
end Graph189GlobalOrder
