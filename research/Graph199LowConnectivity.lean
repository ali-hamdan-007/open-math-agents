import Graph199H1Assemble

namespace Graph199
open SimpleGraph

/-- Every graph in conjecture 199 with vertex connectivity at most two has a
Hamiltonian path, with no remaining block or cut hypotheses. -/
theorem conjecture199_of_connectivity_le_two
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    (hc : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hk : vertexConnectivity G ≤ 2) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases h₁ : vertexConnectivity G ≤ 1
  · exact conjecture199_of_connectivity_le_one hc ht h₁
  by_cases hi : G.indepNum ≤ 2
  · exact conjecture199_of_indepNum_le_two hc hi
  exact connectivity_two_reduction h1_two_component_step hc (by omega) (by omega) ht

#print axioms conjecture199_of_connectivity_le_two
end Graph199
