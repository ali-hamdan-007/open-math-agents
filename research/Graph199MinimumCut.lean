import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.Connectivity

namespace Graph199

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Removing fewer vertices than the vertex connectivity leaves a connected graph. -/
theorem connected_of_card_lt_vertexConnectivity (T : Finset V)
    (hT : T.card < vertexConnectivity G) :
    (G.induce ((T : Set V)ᶜ)).Connected := by
  classical
  by_contra hn
  have hk : vertexConnectivity G ≤ T.card := by
    unfold vertexConnectivity
    split_ifs
    · omega
    · exact csInf_le' ⟨T, rfl, Or.inl hn⟩
  omega

/-- Every vertex of a minimum cut has a neighbor on either side of a nontrivial
separation of the remaining vertices. The set `L` can be the support of any one
connected component. -/
theorem minCut_adj_side (S : Finset V) (u : V) (hu : u ∈ S)
    (hS : S.card ≤ vertexConnectivity G) (L : Set V)
    (hL : ∃ x ∈ L, x ∉ S) (hR : ∃ y ∉ L, y ∉ S)
    (hcross : ∀ x ∈ L, ∀ y ∉ L, x ∉ S → y ∉ S → ¬ G.Adj x y) :
    ∃ x ∈ L, x ∉ S ∧ G.Adj u x := by
  classical
  by_contra hn
  obtain ⟨x, hx, hxs⟩ := hL
  obtain ⟨y, hy, hys⟩ := hR
  let T := S.erase u
  have hT : T.card < vertexConnectivity G :=
    (Finset.card_erase_lt_of_mem hu).trans_le hS
  let K := G.induce ((T : Set V)ᶜ)
  have hK : K.Connected := connected_of_card_lt_vertexConnectivity T hT
  let a : ↥((T : Set V)ᶜ) := ⟨x, fun hx' => hxs (mem_of_mem_erase hx')⟩
  let b : ↥((T : Set V)ᶜ) := ⟨y, fun hy' => hys (mem_of_mem_erase hy')⟩
  have step (c d : ↥((T : Set V)ᶜ)) (hcd : K.Adj c d)
      (hc : c.val ∈ L ∧ c.val ∉ S) : d.val ∈ L ∧ d.val ∉ S := by
    have hda : G.Adj c.val d.val := hcd
    have hds : d.val ∉ S := by
      intro hm
      have hdu : d.val = u := by
        by_contra hne
        exact d.property (mem_erase.mpr ⟨hne, hm⟩)
      apply hn
      exact ⟨c.val, hc.1, hc.2, hdu ▸ hda.symm⟩
    exact ⟨by_contra (fun hd => hcross c.val hc.1 d.val hd hc.2 hds hda), hds⟩
  have closed {c : ↥((T : Set V)ᶜ)} (hc : Relation.ReflTransGen K.Adj a c) :
      c.val ∈ L ∧ c.val ∉ S := by
    induction hc with
    | refl => exact ⟨hx, hxs⟩
    | tail _ hadj ih => exact step _ _ hadj ih
  exact hy (closed ((K.reachable_iff_reflTransGen a b).mp (hK a b))).1

#print axioms minCut_adj_side

end Graph199
