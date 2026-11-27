import Graph199AmbientSeparator
import Mathlib.Combinatorics.SimpleGraph.Tutte

namespace Graph199
open SimpleGraph Finset

/-- For graphs of even order the unrestricted component bound implies a
perfect matching, by the parity of the odd components and Tutte's theorem. -/
theorem perfect_matching_of_component_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (he : Even (Nat.card V))
    (hc : ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  apply G.tutte.mpr
  intro S hv
  let K := (⊤ : G.Subgraph).deleteVerts S
  have hverts : K.verts = Sᶜ := by ext x; simp [K,Set.mem_compl_iff]
  let e : ↥K.verts ≃ ↥(Sᶜ) := Equiv.setCongr hverts
  let f : K.coe ≃g G.induce (Sᶜ) :=
    ⟨e,by
      intro a b
      change G.Adj a.val b.val ↔ K.Adj a.val b.val
      exact ⟨fun h => (Subgraph.deleteVerts_adj.mpr ⟨Set.mem_univ _,a.property.2,Set.mem_univ _,b.property.2,h⟩),
        fun h => K.adj_sub h⟩⟩
  have hcount := hc S.toFinset
  rw [Set.coe_toFinset] at hcount
  have hodd := K.coe.oddComponents.ncard_le_card
  have hfin : Finite K.coe.ConnectedComponent :=
    Finite.of_surjective K.coe.connectedComponentMk Quot.mk_surjective
  have hc' := Nat.card_congr f.connectedComponentEquiv
  change S.ncard < K.coe.oddComponents.ncard at hv
  have hs : S.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hgap : K.coe.oddComponents.ncard = S.ncard + 1 := by omega
  have hpar := K.coe.odd_ncard_oddComponents
  have hk := Nat.card_congr e
  change Nat.card K.verts = (Sᶜ).ncard at hk
  rw [hk,Set.odd_ncard_compl_iff he, hgap, Nat.odd_add_one] at hpar
  by_cases ho : Odd S.ncard
  · exact (hpar.mpr ho) ho
  · exact ho (hpar.mp ho)

/-- Under the exact induced-tree premise of WOW II 199, even order guarantees
a perfect matching. -/
theorem perfect_matching_of_tree_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nontrivial V] {G : SimpleGraph V} (hG : G.Connected) (he : Even (Nat.card V))
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∃ M : G.Subgraph, M.IsPerfectMatching :=
  perfect_matching_of_component_bound he (all_separator_component_bound hG ht)

#print axioms perfect_matching_of_tree_bound
end Graph199
