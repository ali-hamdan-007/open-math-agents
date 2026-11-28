import Graph189CompletionConnectivity

namespace Graph189UniversalCycle
open SimpleGraph Finset

/-- A vertex whose deletion retains the original connectivity can serve as the
universal completion vertex and raises connectivity by at least one. -/
theorem completeAt_connectivity_of_removable {V : Type*} [Fintype V] [Nontrivial V]
    [DecidableEq V] (G : SimpleGraph V) (z : V) [Nontrivial {v : V // v ≠ z}]
    (room : G.vertexConnectivity < Fintype.card V - 1)
    (retains : G.vertexConnectivity ≤ (G.induce {v : V | v ≠ z}).vertexConnectivity) :
    G.vertexConnectivity + 1 ≤ (completeAt G z).vertexConnectivity := by
  classical
  apply completeAt_connectivity_add_one z room
  intro T size contains
  let R := (univ : Finset {v : V // v ≠ z}).filter (fun v => v.val ∈ T)
  let incl : {v : V // v ≠ z} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have mapped : R.map incl = T.erase z := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := mem_map.mp hv
      exact mem_erase.mpr ⟨u.property,(mem_filter.mp hu).2⟩
    · intro hv
      obtain ⟨hne,hin⟩ := mem_erase.mp hv
      exact mem_map.mpr ⟨⟨v,hne⟩,mem_filter.mpr ⟨mem_univ _,hin⟩,rfl⟩
  have cr : R.card < (G.induce {v : V | v ≠ z}).vertexConnectivity := by
    have h₁ := congrArg Finset.card mapped
    rw [card_map,card_erase_of_mem contains] at h₁
    have h₂ := card_pos.mpr ⟨z,contains⟩
    omega
  have c := Graph189CutSides.connected_after_smaller_deletion R cr
  let f : ((G.induce {v : V | v ≠ z}).induce {v | v ∉ R}) →g
      (G.induce {v : V | v ∉ T}) := {
    toFun := fun v => ⟨v.val.val,fun h => v.property (mem_filter.mpr ⟨mem_univ _,h⟩)⟩
    map_rel' := fun h => h }
  apply c.map f
  intro v
  have ne : v.val ≠ z := by
    intro eq
    exact v.property (eq ▸ contains)
  refine ⟨⟨⟨v.val,ne⟩,?_⟩,rfl⟩
  exact fun h => v.property (mem_filter.mp h).2

#print axioms completeAt_connectivity_of_removable
end Graph189UniversalCycle
