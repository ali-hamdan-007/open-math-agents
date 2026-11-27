import Graph199Cut
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Graph199
open SimpleGraph Finset

/-- A maximum independent set lies in one connected component of the complement.
A vertex in a different component is a common neighbor in the original graph.
Together they induce a star on one more vertex than the independence number. -/
theorem indepNum_add_one_le_tree_of_compl_disconnected
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hd : ¬ Gᶜ.Connected) :
    G.indepNum + 1 ≤ largestInducedTreeSize G := by
  classical
  obtain ⟨S,hS⟩ := G.maximumIndepSet_exists
  have card := G.maximumIndepSet_card_eq_indepNum S hS
  rw [← card]
  have common : ∃ z, ∀ y ∈ S, G.Adj z y := by
    by_cases hne : S.Nonempty
    · obtain ⟨x,hx⟩ := hne
      obtain ⟨z,hz⟩ : ∃ z, ¬ Gᶜ.Reachable x z := by
        by_contra! h
        exact hd (Gᶜ.connected_iff_exists_forall_reachable.mpr ⟨x,h⟩)
      refine ⟨z,fun y hy => ?_⟩
      have hxy : Gᶜ.Reachable x y := by
        by_cases he : x = y
        · exact he ▸ Reachable.rfl
        · exact ((G.compl_adj x y).mpr ⟨he,hS.isIndepSet hx hy he⟩).reachable
      have hn : ¬Gᶜ.Reachable y z := fun h => hz (hxy.trans h)
      have e := (Gᶜ.reachable_or_compl_adj y z).resolve_left hn
      simpa using e.symm
    · exact ⟨Classical.arbitrary V,fun y hy => (hne ⟨y,hy⟩).elim⟩
  obtain ⟨z,hz⟩ := common
  exact star_bound z S hS.isIndepSet hz

/-- The conjecture's tree bound implies the Chvátal–Erdős numerical
traceability condition when the complement is disconnected. -/
theorem indepNum_le_connectivity_add_one_of_compl_disconnected
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) (hd : ¬ Gᶜ.Connected)
    (h : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    G.indepNum ≤ vertexConnectivity G + 1 := by
  have := indepNum_add_one_le_tree_of_compl_disconnected G hd
  omega

#print axioms indepNum_le_connectivity_add_one_of_compl_disconnected
end Graph199
