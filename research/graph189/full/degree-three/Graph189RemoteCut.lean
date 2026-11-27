import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace Graph189RemoteCut

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The closed neighborhood in the graph induced on the remote vertices. -/
def closedRemote (x : V) : Finset V :=
  insert x (G.neighborFinset x)

theorem mem_closedRemote {x y : V} :
    y ∈ closedRemote G x ↔ y = x ∨ G.Adj x y := by
  simp [closedRemote]

/-- Two remote balls on opposite sides of the cut overlap only in the boundary. -/
theorem opposed_balls {K D L : Finset V} {x y : V}
    (hcover : ∀ v : V, v ∈ K ∨ v ∈ D ∨ v ∈ L)
    (hdisj : Disjoint K L) (hcut : ∀ a ∈ K, ∀ b ∈ L, ¬ G.Adj a b)
    (hx : x ∈ K) (hy : y ∈ L) :
    closedRemote G x ⊆ K ∪ D ∧ closedRemote G y ⊆ L ∪ D ∧
    closedRemote G x ∩ closedRemote G y ⊆ D := by
  have hK : closedRemote G x ⊆ K ∪ D := by
    intro v hv
    rcases hcover v with h | h | h
    · exact mem_union_left _ h
    · exact mem_union_right _ h
    · rcases (mem_closedRemote G).mp hv with rfl | he
      · exact (disjoint_left.mp hdisj hx h).elim
      · exact (hcut x hx v h he).elim
  have hL : closedRemote G y ⊆ L ∪ D := by
    intro v hv
    rcases hcover v with h | h | h
    · rcases (mem_closedRemote G).mp hv with rfl | he
      · exact (disjoint_left.mp hdisj h hy).elim
      · exact (hcut v h y hy he.symm).elim
    · exact mem_union_right _ h
    · exact mem_union_left _ h
  refine ⟨hK,hL,?_⟩
  intro v hv
  obtain ⟨hvx,hvy⟩ := mem_inter.mp hv
  rcases mem_union.mp (hK hvx) with h | h
  · rcases mem_union.mp (hL hvy) with h' | h'
    · exact (disjoint_left.mp hdisj h h').elim
    · exact h'
  · exact h

/-- A private vertex cannot see both deep sides of the remote cut. -/
theorem private_confined {K D L R H : Finset V} {k : ℕ} {t : V}
    (hcover : ∀ v : V, v ∈ K ∨ v ∈ D ∨ v ∈ L)
    (hdisj : Disjoint K L) (hcut : ∀ a ∈ K, ∀ b ∈ L, ¬ G.Adj a b)
    (hD : D.card ≤ 3) (ht : t ∈ K) (hk : 5 ≤ k)
    (hball : ∀ x : V, x ≠ t → k - 1 ≤ (closedRemote G x).card)
    (hsub : ∀ x ∈ R, closedRemote G x ⊆ H)
    (hH : H.card ≤ 2 * k - 7)
    {x y : V} (hx : x ∈ K.erase t) (hy : y ∈ L) (hxR : x ∈ R) (hyR : y ∈ R) :
    False := by
  obtain ⟨hxt,hxK⟩ := mem_erase.mp hx
  have hyt : y ≠ t := fun h => disjoint_left.mp hdisj (h ▸ ht) hy
  have hInter := (opposed_balls G hcover hdisj hcut hxK hy).2.2
  have hI := card_le_card hInter
  have hU := card_le_card (union_subset (hsub x hxR) (hsub y hyR))
  have hCard := card_union_add_card_inter (closedRemote G x) (closedRemote G y)
  have hX := hball x hxt
  have hY := hball y hyt
  omega

/-- A sole private class covers the deep side, which is too large for the common representative. -/
theorem singleton_remote_cut {K D L S : Finset V} {R H : Fin 3 → Finset V} {k : ℕ} {t : V}
    (hcover : ∀ v : V, v ∈ K ∨ v ∈ D ∨ v ∈ L)
    (hdisj : Disjoint K L) (hcut : ∀ a ∈ K, ∀ b ∈ L, ¬ G.Adj a b)
    (hD : D.card ≤ 3) (ht : t ∈ K) (hk : 5 ≤ k)
    (hball : ∀ x : V, x ≠ t → k - 1 ≤ (closedRemote G x).card)
    (hsub : ∀ i x, x ∈ R i → closedRemote G x ⊆ H i)
    (hH : ∀ i, (H i).card ≤ 2 * k - 7)
    (hR : ∀ i, (R i).card ≤ k - 2)
    (hpriv : ∀ x : V, x ≠ t → ∃ i, x ∈ R i)
    (hK : k ≤ K.card) (hL : L.Nonempty)
    (hStrong : ∀ x i, x ≠ t → x ∈ R i → (∀ j, x ∈ R j → j = i) →
      k ≤ (closedRemote G x).card)
    (hS : S.Nonempty) (hSL : Disjoint S L)
    (hcap : ∀ i, ((R i \ {t}) ∪ S).card ≤ k - 3) :
    False := by
  obtain ⟨y,hy⟩ := hL
  have hyt : y ≠ t := fun h => disjoint_left.mp hdisj (h ▸ ht) hy
  obtain ⟨h,hyR⟩ := hpriv y hyt
  have hxcover : ∃ x, x ∈ K.erase t := by
    have hc := card_erase_add_one ht
    exact card_pos.mp (by omega)
  obtain ⟨x,hx⟩ := hxcover
  obtain ⟨i,hxi⟩ := hpriv x (mem_erase.mp hx).1
  have hih : i ≠ h := by
    rintro rfl
    exact private_confined G hcover hdisj hcut hD ht hk hball (hsub i) (hH i) hx hy hxi hyR
  have hjexists : ∃ z ∈ K.erase t, ∃ j, j ≠ i ∧ z ∈ R j := by
    by_contra he
    have hKi : K.erase t ⊆ R i := by
      intro z hz
      obtain ⟨j,hzj⟩ := hpriv z (mem_erase.mp hz).1
      by_cases hji : j = i
      · simpa [hji] using hzj
      · exact (he ⟨z,hz,j,hji,hzj⟩).elim
    have hc := card_erase_add_one ht
    have hle := card_le_card hKi
    have hr := hR i
    omega
  obtain ⟨z,hz,j,hji,hzj⟩ := hjexists
  have hjh : j ≠ h := by
    rintro rfl
    exact private_confined G hcover hdisj hcut hD ht hk hball (hsub j) (hH j) hz hy hzj hyR
  have hexcl : ∀ v ∈ L, ∀ l, v ∈ R l → l = h := by
    intro v hv l hvl
    have hli : l ≠ i := by
      rintro rfl
      exact private_confined G hcover hdisj hcut hD ht hk hball (hsub l) (hH l) hx hv hxi hvl
    have hlj : l ≠ j := by
      rintro rfl
      exact private_confined G hcover hdisj hcut hD ht hk hball (hsub l) (hH l) hz hv hzj hvl
    have hfin : ∀ a b c d : Fin 3, a ≠ b → a ≠ c → b ≠ c →
      d ≠ a → d ≠ b → d = c := by
      intro a b c d hab hac hbc hda hdb
      apply Fin.ext
      have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
      have hac' : a.val ≠ c.val := fun e => hac (Fin.ext e)
      have hbc' : b.val ≠ c.val := fun e => hbc (Fin.ext e)
      have hda' : d.val ≠ a.val := fun e => hda (Fin.ext e)
      have hdb' : d.val ≠ b.val := fun e => hdb (Fin.ext e)
      omega
    exact hfin i j h l (Ne.symm hji) hih hjh hli hlj
  have hLR : L ⊆ R h \ {t} := by
    intro v hv
    have hvt : v ≠ t := fun e => disjoint_left.mp hdisj (e ▸ ht) hv
    obtain ⟨l,hvl⟩ := hpriv v hvt
    exact mem_sdiff.mpr ⟨hexcl v hv l hvl ▸ hvl, by simpa using hvt⟩
  have hOrd := (opposed_balls G hcover hdisj hcut (mem_erase.mp hx).2 hy).2.1
  have hBig := hStrong y h hyt hyR (hexcl y hy)
  have hu := card_le_card hOrd
  have hld := card_union_le L D
  have hc := hcap h
  have hs := card_pos.mpr hS
  have hLS := card_le_card (union_subset_union hLR (Subset.refl S))
  rw [card_union_of_disjoint hSL.symm] at hLS
  omega

#print axioms Graph189RemoteCut.singleton_remote_cut

end Graph189RemoteCut
