import Graph189Structural
import Graph189ThirdConnectivity

namespace Graph189LargeDegree
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A qualifying graph with second-smallest degree at least 26 and vertex
connectivity at least five has a Hamiltonian path, at every graph order. -/
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (high : 26≤G.secondSmallestDegree) (connected : 5≤G.vertexConnectivity) :
    ∃ a b : V, ∃ p : G.Walk a b,p.IsHamiltonian := by
  rcases lt_or_ge (3*G.vertexConnectivity) G.secondSmallestDegree with low|large
  · exact Graph189Structural.traceable hc cap connected high low
  · exact Graph189ThirdConnectivity.traceable hc cap (by omega) large

#print axioms traceable
end Graph189LargeDegree
