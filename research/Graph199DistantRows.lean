import Graph199EndpointChoice
import Graph199ChosenBlocks
import Graph199ComponentLeafPools

namespace Graph199

open Finset SimpleGraph

variable {V I : Type*} [Fintype V] [DecidableEq I] {G : SimpleGraph V}

/-- A sequence whose nonconsecutive centers neither see each other nor meet
the same component forces a large induced tree. At either end, the tree uses
either the endpoint and its private leaves or leaves from the shared components. -/
theorem large_tree_of_distant_rows {d : ℕ} (hd : 2 ≤ d)
    (c : Fin (d+1) ↪ V) (C : I → Set V) (R : Fin (d+1) → Finset I)
    (touch : ∀ i k, k ∈ R i ↔ ∃ x ∈ C k, G.Adj (c i) x)
    (outside : ∀ i k, c i ∉ C k)
    (separate : ∀ i j, i ≠ j → ∀ x ∈ C i, ∀ y ∈ C j, x ≠ y ∧ ¬ G.Adj x y)
    (conn : ∀ k, (G.induce (C k)).Connected)
    (consec : ∀ j : Fin d, G.Adj (c j.castSucc) (c j.succ) ∨
      ∃ k, k ∈ R j.castSucc ∧ k ∈ R j.succ)
    (close : ∀ i j, G.Adj (c i) (c j) → i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1)
    (near : ∀ i j k, k ∈ R i → k ∈ R j → i.val ≤ j.val + 1 ∧ j.val ≤ i.val + 1) :
    2*d + (R 0).card + (R (Fin.last d)).card ≤ 2 * largestInducedTreeSize G := by
  classical
  let a : Fin (d+1) := 0
  let b : Fin (d+1) := ⟨1,by omega⟩
  let y : Fin (d+1) := ⟨d-1,by omega⟩
  let z : Fin (d+1) := Fin.last d
  let JL := endpointPool (R a) (R b)
  let JR := endpointPool (R z) (R y)
  let l := endpointDrop (R a) (R b)
  let r := endpointDrop (R z) (R y)
  let n := d-l-r
  have ha : a.val = 0 := rfl
  have hb : b.val = 1 := rfl
  have hy : y.val = d-1 := rfl
  have hz : z.val = d := rfl
  have hl (hk : endpointKeeps (R a) (R b) = true) : l = 0 := by simp [l,endpointDrop,hk]
  have hl' (hk : endpointKeeps (R a) (R b) = false) : l = 1 := by simp [l,endpointDrop,hk]
  have hr (hk : endpointKeeps (R z) (R y) = true) : r = 0 := by simp [r,endpointDrop,hk]
  have hr' (hk : endpointKeeps (R z) (R y) = false) : r = 1 := by simp [r,endpointDrop,hk]
  have hlb : l ≤ 1 := by cases h : endpointKeeps (R a) (R b) <;> simp [l,endpointDrop,h]
  have hrb : r ≤ 1 := by cases h : endpointKeeps (R z) (R y) <;> simp [r,endpointDrop,h]
  have hend : l+n = d-r := by dsimp [n]; omega
  let eL : Fin (d+1) := ⟨l,by omega⟩
  let eR : Fin (d+1) := ⟨d-r,by omega⟩
  have heL : eL.val = l := rfl
  have heR : eR.val = d-r := rfl
  have hLsub : JL ⊆ R a := endpoint_pool_subset _ _
  have hRsub : JR ⊆ R z := endpoint_pool_subset _ _
  have hJustL i k (hk : k ∈ JL) (hm : k ∈ R i) (hi : l ≤ i.val) :
      i = eL := by
    have h := near a i k (hLsub hk) hm
    apply Fin.ext
    rw [heL]
    cases hK : endpointKeeps (R a) (R b)
    · have := hl' hK
      omega
    · have hh : k ∉ R b := (mem_sdiff.mp (by simpa [JL,endpointPool,hK] using hk)).2
      have hne : i.val ≠ 1 := fun he => hh (Fin.ext (he.trans hb.symm) ▸ hm)
      have := hl hK
      omega
  have hJustR i k (hk : k ∈ JR) (hm : k ∈ R i) (hi : i.val ≤ l+n) :
      i = eR := by
    have h := near z i k (hRsub hk) hm
    apply Fin.ext
    rw [heR]
    cases hK : endpointKeeps (R z) (R y)
    · have := hr' hK
      omega
    · have hh : k ∉ R y := (mem_sdiff.mp (by simpa [JR,endpointPool,hK] using hk)).2
      have hne : i.val ≠ d-1 := fun he => hh (Fin.ext (he.trans hy.symm) ▸ hm)
      have := hr hK
      omega
  have hMeetL k (hk : k ∈ JL) : k ∈ R eL := by
    cases hK : endpointKeeps (R a) (R b)
    · have he : eL = b := Fin.ext (by rw [heL,hl' hK,hb])
      rw [he]
      exact (mem_inter.mp (by simpa [JL,endpointPool,hK] using hk)).2
    · have he : eL = a := Fin.ext (by rw [heL,hl hK,ha])
      rw [he]
      exact hLsub hk
  have hMeetR k (hk : k ∈ JR) : k ∈ R eR := by
    cases hK : endpointKeeps (R z) (R y)
    · have he : eR = y := Fin.ext (by rw [heR,hr' hK,hy])
      rw [he]
      exact (mem_inter.mp (by simpa [JR,endpointPool,hK] using hk)).2
    · have he : eR = z := Fin.ext (by rw [heR,hr hK,hz,Nat.sub_zero])
      rw [he]
      exact hRsub hk
  obtain ⟨B,hav,hdis,hcross,hinc,hcon,hBspec⟩ :=
    chosen_bridging_blocks c C R touch outside separate conn consec near
  obtain ⟨D,hD,hDcent,hDcard,hDtree⟩ :=
    connector_of_ordered_interval c B hav hdis hcross close hinc hcon l n (by omega)
  have hleft : c eL ∈ D := hDcent eL (by rw [heL]) (by rw [heL]; omega)
  have hright : c eR ∈ D := hDcent eR (by omega) (by rw [heR,hend])
  have hpool : Disjoint JL JR := by
    apply Finset.disjoint_left.mpr
    intro k hL hR
    have hh := near a z k (hLsub hL) (hRsub hR)
    omega
  have hblock (k : I) (hk : k ∈ JL ∨ k ∈ JR) (j : Fin d)
      (hlj : l ≤ j.val) (hrj : j.val < l+n)
      {x : V} (hx : x ∈ C k) {w : V} (hw : w ∈ B j) : x ≠ w ∧ ¬ G.Adj x w := by
    obtain ⟨t,ht,htL,htR⟩ := hBspec j w hw
    refine separate k t ?_ x hx w ht
    rintro rfl
    rcases hk with hk | hk
    · have e1 := congrArg Fin.val (hJustL _ _ hk htL (by simpa using hlj))
      have e2 := congrArg Fin.val (hJustL _ _ hk htR (by simp; omega))
      simp only [Fin.val_castSucc,Fin.val_succ] at e1 e2
      omega
    · have e1 := congrArg Fin.val (hJustR _ _ hk htL (by simp; omega))
      have e2 := congrArg Fin.val (hJustR _ _ hk htR (by simp; omega))
      simp only [Fin.val_castSucc,Fin.val_succ] at e1 e2
      omega
  have hOutside k (hk : k ∈ JL ∪ JR) : Disjoint (C k) (D : Set V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxD
    rcases hD x hxD with ⟨i,_,_,rfl⟩ | ⟨j,hj,hj',hxB⟩
    · exact outside i k hx
    · exact (hblock k (mem_union.mp hk) j hj hj' hx hxB).1 rfl
  have hOnlyL k (hk : k ∈ JL) x (hx : x ∈ C k) w (hw : w ∈ D) (he : G.Adj x w) :
      w = c eL := by
    rcases hD w hw with ⟨i,hi,_,rfl⟩ | ⟨j,hj,hj',hwB⟩
    · rw [hJustL i k hk ((touch i k).mpr ⟨x,hx,he.symm⟩) hi]
    · exact False.elim ((hblock k (Or.inl hk) j hj hj' hx hwB).2 he)
  have hOnlyR k (hk : k ∈ JR) x (hx : x ∈ C k) w (hw : w ∈ D) (he : G.Adj x w) :
      w = c eR := by
    rcases hD w hw with ⟨i,_,hi,rfl⟩ | ⟨j,hj,hj',hwB⟩
    · rw [hJustR i k hk ((touch i k).mpr ⟨x,hx,he.symm⟩) hi]
    · exact False.elim ((hblock k (Or.inr hk) j hj hj' hx hwB).2 he)
  have ht := component_leaf_pools_bound D C JL JR (c eL) (c eR) hDtree
    hleft hright hpool separate hOutside (fun k hk => by
      obtain ⟨x,hx,he⟩ := (touch _ _).mp (hMeetL k hk)
      exact ⟨x,hx,he.symm⟩)
    (fun k hk => by
      obtain ⟨x,hx,he⟩ := (touch _ _).mp (hMeetR k hk)
      exact ⟨x,hx,he.symm⟩) hOnlyL hOnlyR
  have hGainL := endpoint_pool_gain (R a) (R b)
  have hGainR := endpoint_pool_gain (R z) (R y)
  change (R a).card + 1 + 2*l ≤ 2*JL.card + 2 at hGainL
  change (R z).card + 1 + 2*r ≤ 2*JR.card + 2 at hGainR
  change 2*d + (R a).card + (R z).card ≤ _
  omega

#print axioms large_tree_of_distant_rows

end Graph199
