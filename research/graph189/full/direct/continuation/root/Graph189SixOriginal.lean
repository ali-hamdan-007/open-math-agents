import Graph189SixAllConnected
import Graph189SixOrder

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
  exact Graph189SixAllConnected.large hc cap degree (by omega)

#print axioms traceable_six
end Graph189SixOriginal
