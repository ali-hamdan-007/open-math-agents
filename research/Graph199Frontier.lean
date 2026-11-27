import Graph199Complement
import Graph199Chvatal
import Graph199LowConnectivity

namespace Graph199
open SimpleGraph

/-- Conjecture 199 holds for connected graphs with disconnected complement.
This includes every nontrivial complete join. -/
theorem conjecture199_of_compl_disconnected {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hc : G.Connected) (hd : ¬ Gᶜ.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let _ : Nonempty V := hc.nonempty
  exact hamiltonian_of_indepNum_le_vertexConnectivity_add_one hc
    (indepNum_le_connectivity_add_one_of_compl_disconnected G hd ht)

/-- Any counterexample has connectivity at least three, connected complement,
and an independent set of size at least two greater than its connectivity. -/
theorem necessary_conditions_of_nontraceable
    {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] (G : SimpleGraph V)
    (hc : G.Connected) (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hn : ¬ ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian) :
    3 ≤ vertexConnectivity G ∧ Gᶜ.Connected ∧ vertexConnectivity G + 2 ≤ G.indepNum := by
  refine ⟨?_,?_,?_⟩
  · by_contra! h
    exact hn (conjecture199_of_connectivity_le_two G hc ht (by omega))
  · by_contra h
    exact hn (conjecture199_of_compl_disconnected hc h ht)
  · by_contra! h
    exact hn (hamiltonian_of_indepNum_le_vertexConnectivity_add_one hc (by omega))

#print axioms conjecture199_of_compl_disconnected
#print axioms necessary_conditions_of_nontraceable
end Graph199
