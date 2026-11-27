import Graph199DenseCut
import Graph199RestoreCut

namespace Graph199
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}

/-- At vertex connectivity three, the tree hypothesis in WOWII #199
implies the component-count condition for every deleted vertex set. -/
theorem all_separator_component_bound_of_connectivity_three (hG : G.Connected)
    (hk : vertexConnectivity G = 3)
    (ht : largestInducedTreeSize G - 2 ≤ vertexConnectivity G) :
    ∀ U : Finset V, Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent ≤ U.card + 1 := by
  classical
  by_contra! hbad
  let S : Set ℕ := {n | ∃ U : Finset V, U.card = n ∧
    U.card + 1 < Nat.card (G.induce ((U : Set V)ᶜ)).ConnectedComponent}
  have hS : S.Nonempty := by
    obtain ⟨U,hU⟩ := hbad
    exact ⟨U.card,U,rfl,hU⟩
  obtain ⟨U,hCard,hU⟩ := Nat.sInf_mem hS
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
  have hGood := separator_component_bound_of_min_row hG U
    (fun u => by rw [hk]; exact hnear u) ht
  omega

#print axioms all_separator_component_bound_of_connectivity_three
end Graph199
