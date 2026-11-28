import Graph189WidthInterval
import Graph189ScalarReplay

namespace Graph189WidthInterval
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Every counterexample to the original conjecture passes the exact Boolean
widthPossible from the independently executed scalar projection. -/
theorem replay_widthPossible (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (hn : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    Graph189ScalarReplay.widthPossible G.secondSmallestDegree (Fintype.card V) = true := by
  simpa [Graph189ScalarReplay.widthPossible, Graph189ScalarReplay.ceilDiv, low, difference]
    using necessary_interval hc hcap hn

#print axioms replay_widthPossible
end Graph189WidthInterval
