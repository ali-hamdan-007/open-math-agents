import Graph189LowDeletionTraceable
import Graph189ConnectivityDegree
import Graph189QuarterOrder
import Graph189ActualScalarWidth
import Graph189NearMinimumDegree

open Finset SimpleGraph
namespace Graph189StructuralConclusion
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At second-smallest degree at least 26, a Hamilton path after deleting
a minimum-degree vertex gives a Hamilton path in the full graph whenever
the minimum degree is at least three. This includes small vertex cuts. -/
theorem traceable_of_traceable_minimum_deletion (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hk : 26 ≤ G.secondSmallestDegree)
    (z : V) (minimum : G.degree z=G.minDegree) (three : 3 ≤ G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian) :
    ∃ u v : V, ∃ q : G.Walk u v, q.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  let f := G.degree z
  let n := Fintype.card V
  let l := (k+2)/4
  change 26 ≤ k at hk
  have point (v : V) : G.distEven v ≤ k+1 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    change _ ≤ 1+k at h
    omega
  by_cases lowratio : 3*f<k
  · exact nontrace (Graph189ExteriorGap.traceable_of_low_deletion hc z point p hp three lowratio)
  have low := Graph189ExteriorDegreeCycle.low_of_traceable_minimum_deletion
    (by change 5 ≤ k; omega) point nontrace z minimum p hp
  have lower : (l+1)*(k-l+2) ≤ n+1 :=
    Graph189ExteriorGap.order_of_traceable_low_deletion z low point nontrace p hp
      (by dsimp [l]; omega : 3 ≤ l) (by change 2*l ≤ k; dsimp [l]; omega)
      (by change l ≤ f; dsimp [l]; omega)
  have base := (Graph189QuarterOrder.lower_estimates hk lower).1
  have width := Graph189ActualScalarWidth.bounds hc cap nontrace (by change 4*k+2 ≤ n; omega)
  exact Graph189QuarterOrder.impossible hk lower width.1 width.2.1 width.2.2.2.1 width.2.2.2.2

#print axioms traceable_of_traceable_minimum_deletion
end Graph189StructuralConclusion
