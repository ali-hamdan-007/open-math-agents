import Graph189MinimumCutOrder

open SimpleGraph Finset
namespace Graph189CutSides
variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting all neighbors of a vertex isolates it. The complete graph
convention for vertex connectivity also gives the claimed degree bound. -/
theorem connectivity_le_degree (z : V) : G.vertexConnectivity ≤ G.degree z := by
  classical
  let S := G.neighborFinset z
  have sz : S.card=G.degree z := G.card_neighborFinset_eq_degree z
  have convention : G.vertexConnectivity ≤ Fintype.card V-1 := by
    unfold vertexConnectivity
    rw [if_neg (not_le.mpr (Fintype.one_lt_card (α:=V)))]
    exact Nat.sInf_le ⟨univ.erase z,by simp,Or.inr (by simp)⟩
  by_contra! fail
  have conn := connected_after_smaller_deletion (G:=G) S (sz ▸ fail)
  let W := {v : V | v ∉ S}
  let z' : W := ⟨z, show z ∉ G.neighborFinset z by simp⟩
  have card : 1 < Fintype.card W := by
    have same : W = ((Sᶜ : Finset V) : Set V) := by ext v; simp [W]
    rw [Fintype.card_congr (Equiv.setCongr same)]
    change 1 < Fintype.card (Sᶜ : Finset V)
    rw [Fintype.card_coe,Finset.card_compl]
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp card
  obtain ⟨w,edge⟩ := conn.preconnected.exists_adj_of_nontrivial z'
  exact w.property ((G.mem_neighborFinset z w.val).mpr edge)

#print axioms connectivity_le_degree
end Graph189CutSides
