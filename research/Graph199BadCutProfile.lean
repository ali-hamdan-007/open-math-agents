import Graph199KappaThreeCut
import Graph199LargeCut

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

/-- A failure of the component-count condition has a minimum-cardinality
witness of size at least three times vertex connectivity. Each of its
vertices meets at least three components, and one meets fewer than κ. -/
theorem exists_bad_separator_profile (hG : G.Connected)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G)
    (hbad : ∃ U : Finset V, U.card + 1 <
      Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent) :
    ∃ U : Finset V, U.card + 1 < Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ∧
      3 * vertexConnectivity G ≤ U.card ∧
      (∀ u : U, 3 ≤ {i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent |
        MeetsComponent U u.val i}.ncard) ∧
      ∃ u : U, {i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent |
        MeetsComponent U u.val i}.ncard < vertexConnectivity G := by
  classical
  let S : Set ℕ := {n | ∃ U : Finset V, U.card = n ∧
    U.card + 1 < Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent}
  have hS : S.Nonempty := by
    obtain ⟨U,hU⟩ := hbad
    exact ⟨U.card,U,rfl,hU⟩
  obtain ⟨U,hCard,hU⟩ := Nat.sInf_mem hS
  have hsize : 3 * vertexConnectivity G ≤ U.card := by
    by_contra! hn
    exact (not_le.mpr hU) (separator_component_bound_lt_three hG U hn ht)
  have hnear (u : U) :
      3 ≤ {i : (G.induce ((U : Set V)ᶜ)).ConnectedComponent |
        MeetsComponent U u.val i}.ncard := by
    let T := U.erase u.val
    have hGood : Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent ≤ T.card + 1 := by
      by_contra! ht'
      have hle : sInf S ≤ T.card := csInf_le' ⟨T,rfl,ht'⟩
      have hlt : T.card < U.card := card_erase_lt_of_mem u.property
      omega
    have hRest := restore_cut_component_bound (G := G) U u.val u.property
    change Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent + 1 ≤
      Nat.card (G.induce ((T : Set V)ᶜ)).ConnectedComponent + _ at hRest
    have hEq : T.card = U.card - 1 := card_erase_of_mem u.property
    have hPos : 0 < U.card := card_pos.mpr ⟨u.val,u.property⟩
    omega
  refine ⟨U,hU,hsize,hnear,?_⟩
  by_contra! h
  exact (not_le.mpr hU) (separator_component_bound_of_min_row hG U h ht)

#print axioms exists_bad_separator_profile
end Graph199
