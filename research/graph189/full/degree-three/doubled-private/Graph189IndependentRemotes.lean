import Graph189SaturatedDistance

namespace Graph189IndependentRemotes

open SimpleGraph Finset Graph189SaturatedDistance

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors counted in the induced graph on the specified finite vertex set. -/
def neighborsIn (F : Finset V) (x : V) : Finset V :=
  F.filter (G.Adj x)

/-- Closed neighborhood inside the remote layer of the original graph. -/
def closedNeighborsIn (L : Finset V) (x : V) : Finset V :=
  L.filter (fun y => x = y ∨ G.Adj x y)

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem dist_two_of_common_neighbor {x y z : V} (hxy : x ≠ y)
    (hnadj : ¬ G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons hxz (.cons hyz.symm .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hxy hnadj
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega

/-- The two neighbor sets in the complement of the independent set overlap. -/
theorem common_neighbor_of_large_independent_set {F I : Finset V} {k : ℕ}
    (hk : 8 ≤ k) (hFI : I ⊆ F) (hICard : I.card = k - 3)
    (hFCard : 2 * F.card + 15 ≤ 5 * k)
    (hdegree : ∀ x ∈ I, k - 4 ≤ (neighborsIn G F x).card)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    {x y : V} (hx : x ∈ I) (hy : y ∈ I) :
    ∃ z ∈ F \ I, G.Adj x z ∧ G.Adj y z := by
  have hn (v : V) (hv : v ∈ I) : neighborsIn G F v ⊆ F \ I := by
    intro z hz
    obtain ⟨hzF, hvz⟩ := mem_filter.mp hz
    exact mem_sdiff.mpr ⟨hzF, fun hzI => hind v hv z hzI hvz⟩
  have hc := card_sdiff_add_card_eq_card hFI
  have hu := card_le_card (union_subset (hn x hx) (hn y hy))
  have hd := card_inter_add_card_union (neighborsIn G F x) (neighborsIn G F y)
  have hpos : 0 < ((neighborsIn G F x) ∩ (neighborsIn G F y)).card := by
    have := hdegree x hx
    have := hdegree y hy
    omega
  obtain ⟨z, hz⟩ := card_pos.mp hpos
  obtain ⟨hzx, hzy⟩ := mem_inter.mp hz
  exact ⟨z, hn x hx hzx, (mem_filter.mp hzx).2, (mem_filter.mp hzy).2⟩

/-- Common-neighbor overlap gives actual distance two in the full graph. -/
theorem pair_dist_two_of_large_independent_set {F I : Finset V} {k : ℕ}
    (hk : 8 ≤ k) (hFI : I ⊆ F) (hICard : I.card = k - 3)
    (hFCard : 2 * F.card + 15 ≤ 5 * k)
    (hdegree : ∀ x ∈ I, k - 4 ≤ (neighborsIn G F x).card)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    {x y : V} (hx : x ∈ I) (hy : y ∈ I) (hne : x ≠ y) :
    G.dist x y = 2 := by
  obtain ⟨z, _, hxz, hyz⟩ :=
    common_neighbor_of_large_independent_set G hk hFI hICard hFCard hdegree hind hx hy
  exact dist_two_of_common_neighbor G hne (hind x hx y hy) hxz hyz

omit [DecidableRel G.Adj] in
/-- Four common middles and the supporting private's anchor exceed the budget. -/
theorem private_common_middles_le_three [Fintype V]
    {I W : Finset V} {x J b : V} {k : ℕ}
    (hk : 4 ≤ k) (hx : x ∈ I) (hICard : I.card = k - 3)
    (hpair : ∀ y ∈ I.erase x, G.dist x y = 2)
    (hxJ : G.Adj x J) (hJb : G.Adj J b)
    (hJW : ∀ y ∈ W, G.Adj J y)
    (hxb : x ≠ b) (hxbN : ¬ G.Adj x b)
    (hxW : ∀ y ∈ W, x ≠ y ∧ ¬ G.Adj x y)
    (hbW : b ∉ W) (hbI : b ∉ I) (hWI : Disjoint W I)
    (hcap : (evenBall G x).card ≤ k + 1) :
    W.card ≤ 3 := by
  have hfixed (v : V) (hv : v ∈ insert b W) : G.dist x v = 2 := by
    rcases mem_insert.mp hv with rfl | hv
    · exact dist_two_of_common_neighbor G hxb hxbN hxJ hJb.symm
    · exact dist_two_of_common_neighbor G (hxW v hv).1 (hxW v hv).2 hxJ (hJW v hv).symm
  have hdis : Disjoint (I.erase x) (insert b W) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    have hvI := (mem_erase.mp hv).2
    rcases mem_insert.mp hf with rfl | hf
    · exact hbI hvI
    · exact (Finset.disjoint_left.mp hWI hf) hvI
  have h := card_add_le_of_disjoint_distance_two G hpair hfixed hdis hcap
  have hErase := card_erase_add_one hx
  rw [card_insert_of_notMem hbW] at h
  omega

/-- Each low support contains at most four independent vertices. -/
theorem independent_inter_support_card_le_four {L I R H : Finset V} {k : ℕ}
    (hR : R ⊆ H) (hH : (I ∩ R).Nonempty → H.card ≤ k + 1)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hclosed : ∀ x ∈ I ∩ R, closedNeighborsIn G L x ⊆ H)
    (hdegree : ∀ x ∈ I ∩ R, k - 2 ≤ (closedNeighborsIn G L x).card) :
    (I ∩ R).card ≤ 4 := by
  by_cases he : (I ∩ R).Nonempty
  · obtain ⟨x, hx⟩ := he
    have hOutside : ((I ∩ R).erase x) ⊆ H := by
      intro y hy
      exact hR (mem_inter.mp (mem_erase.mp hy).2).2
    have hDis : Disjoint ((I ∩ R).erase x) (closedNeighborsIn G L x) := by
      apply Finset.disjoint_left.mpr
      intro y hy hmem
      obtain ⟨hne, hyI⟩ := mem_erase.mp hy
      rcases (mem_filter.mp hmem).2 with hEq | hAdj
      · exact hne hEq.symm
      · exact hind x (mem_inter.mp hx).1 y (mem_inter.mp hyI).1 hAdj
    have hHCard := hH ⟨x, hx⟩
    have hCard := card_le_card (union_subset hOutside (hclosed x hx))
    rw [card_union_of_disjoint hDis] at hCard
    have hErase := card_erase_add_one hx
    have := hdegree x hx
    omega
  · have hempty : I ∩ R = ∅ := by
      by_contra h
      exact he (nonempty_iff_ne_empty.mpr h)
    simp [hempty]

/-- If only two supports can meet the independent set, both cap-four
estimates together contradict the size of the independent set. -/
theorem two_low_supports_contradiction {L I RB RC HB HC : Finset V} {k : ℕ}
    (hk : 12 ≤ k) (hICard : I.card = k - 3)
    (hcover : I ⊆ RB ∪ RC) (hRB : RB ⊆ HB) (hRC : RC ⊆ HC)
    (hHB : (I ∩ RB).Nonempty → HB.card ≤ k + 1)
    (hHC : (I ∩ RC).Nonempty → HC.card ≤ k + 1)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hclosedB : ∀ x ∈ I ∩ RB, closedNeighborsIn G L x ⊆ HB)
    (hclosedC : ∀ x ∈ I ∩ RC, closedNeighborsIn G L x ⊆ HC)
    (hdegree : ∀ x ∈ I, k - 2 ≤ (closedNeighborsIn G L x).card) :
    False := by
  have hB := independent_inter_support_card_le_four G hRB hHB hind hclosedB
    (fun x hx => hdegree x (mem_inter.mp hx).1)
  have hC := independent_inter_support_card_le_four G hRC hHC hind hclosedC
    (fun x hx => hdegree x (mem_inter.mp hx).1)
  have hsub : I ⊆ (I ∩ RB) ∪ (I ∩ RC) := by
    intro x hx
    rcases mem_union.mp (hcover hx) with h | h
    · exact mem_union_left _ (mem_inter.mpr ⟨hx, h⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hx, h⟩)
  have hCard := card_le_card hsub
  have hUnion := card_union_add_card_inter (I ∩ RB) (I ∩ RC)
  omega

/-- The layer incidences involving one private vertex. -/
structure PrivateGeometry (F : Finset V) where
  privateVertex : V
  anchor : V
  common : Finset V
  privateAnchor : G.Adj privateVertex anchor
  privateCommon : ∀ v ∈ common, G.Adj privateVertex v
  anchorNotCommon : anchor ∉ common
  anchorNotRemote : anchor ∉ F
  commonNotRemote : Disjoint common F
  remotesMissAnchor : ∀ x ∈ F, ¬ G.Adj x anchor
  remotesMissCommon : ∀ x ∈ F, ∀ v ∈ common, ¬ G.Adj x v

/-- The closed hull of a private's support, taken inside the full remote layer. -/
def supportHull (L : Finset V) (J : V) : Finset V :=
  (neighborsIn G L J).biUnion (closedNeighborsIn G L)

theorem closedNeighborsIn_subset_supportHull {L : Finset V} {J x : V}
    (hx : x ∈ neighborsIn G L J) :
    closedNeighborsIn G L x ⊆ supportHull G L J := by
  intro y hy
  exact mem_biUnion.mpr ⟨x, hx, hy⟩

theorem support_subset_supportHull (L : Finset V) (J : V) :
    neighborsIn G L J ⊆ supportHull G L J := by
  intro x hx
  apply closedNeighborsIn_subset_supportHull G hx
  exact mem_filter.mpr ⟨(mem_filter.mp hx).1, Or.inl rfl⟩

/-- The doubled-private counting argument bounds every independent subset of F.
The singleton-anchor privates have the named support and hull bounds. -/
theorem independent_remote_card_bound [Fintype V]
    {F L A : Finset V} {k : ℕ}
    (P Q B C : PrivateGeometry G F)
    (hk : 12 ≤ k) (hFL : F ⊆ L) (hAF : A ⊆ F)
    (hFCard : 2 * F.card + 15 ≤ 5 * k)
    (hdegreeF : ∀ x ∈ F, k - 4 ≤ (neighborsIn G F x).card)
    (hdegreeL : ∀ x ∈ F, k - 2 ≤ (closedNeighborsIn G L x).card)
    (hcap : ∀ x ∈ F, (evenBall G x).card ≤ k + 1)
    (hind : ∀ x ∈ A, ∀ y ∈ A, ¬ G.Adj x y)
    (hcover : ∀ x ∈ F, G.Adj x P.privateVertex ∨ G.Adj x Q.privateVertex ∨
      G.Adj x B.privateVertex ∨ G.Adj x C.privateVertex)
    (hP : 4 ≤ P.common.card) (hQ : 4 ≤ Q.common.card)
    (hRB : (neighborsIn G L B.privateVertex).card ≤ k - 3)
    (hRC : (neighborsIn G L C.privateVertex).card ≤ k - 3)
    (hHB : (supportHull G L B.privateVertex).card ≤
      (neighborsIn G L B.privateVertex).card + B.common.card + 1)
    (hHC : (supportHull G L C.privateVertex).card ≤
      (neighborsIn G L C.privateVertex).card + C.common.card + 1) :
    A.card ≤ k - 4 := by
  by_contra hLarge
  obtain ⟨I, hIA, hICard⟩ := exists_subset_card_eq (s := A) (n := k - 3) (by omega)
  have hIF := hIA.trans hAF
  have hIndI (x : V) (hx : x ∈ I) (y : V) (hy : y ∈ I) := hind x (hIA hx) y (hIA hy)
  have hSmall (J : PrivateGeometry G F) (x : V) (hx : x ∈ I)
      (hxJ : G.Adj x J.privateVertex) : J.common.card ≤ 3 := by
    apply private_common_middles_le_three G (by omega : 4 ≤ k) hx hICard
      _ hxJ J.privateAnchor J.privateCommon _ (J.remotesMissAnchor x (hIF hx))
      _ J.anchorNotCommon _ _ (hcap x (hIF hx))
    · intro y hy
      obtain ⟨hyx, hyI⟩ := mem_erase.mp hy
      exact pair_dist_two_of_large_independent_set G (by omega) hIF hICard hFCard
        (fun v hv => hdegreeF v (hIF hv)) hIndI hx hyI hyx.symm
    · exact fun he => J.anchorNotRemote (he ▸ hIF hx)
    · intro y hy
      exact ⟨fun he => (Finset.disjoint_left.mp J.commonNotRemote hy)
        (he ▸ hIF hx), J.remotesMissCommon x (hIF hx) y hy⟩
    · exact fun h => J.anchorNotRemote (hIF h)
    · exact Disjoint.mono_right hIF J.commonNotRemote
  have hCoverI : I ⊆ neighborsIn G L B.privateVertex ∪ neighborsIn G L C.privateVertex := by
    intro x hx
    rcases hcover x (hIF hx) with hp | hq | hb | hc
    · have := hSmall P x hx hp
      omega
    · have := hSmall Q x hx hq
      omega
    · exact mem_union_left _ (mem_filter.mpr ⟨hFL (hIF hx), hb.symm⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hFL (hIF hx), hc.symm⟩)
  have hHull (J : PrivateGeometry G F)
      (hR : (neighborsIn G L J.privateVertex).card ≤ k - 3)
      (hH : (supportHull G L J.privateVertex).card ≤
        (neighborsIn G L J.privateVertex).card + J.common.card + 1)
      (he : (I ∩ neighborsIn G L J.privateVertex).Nonempty) :
      (supportHull G L J.privateVertex).card ≤ k + 1 := by
    obtain ⟨x, hx⟩ := he
    obtain ⟨hxI, hxJ⟩ := mem_inter.mp hx
    have := hSmall J x hxI (mem_filter.mp hxJ).2.symm
    omega
  exact two_low_supports_contradiction G hk hICard hCoverI
    (support_subset_supportHull G L B.privateVertex) (support_subset_supportHull G L C.privateVertex)
    (hHull B hRB hHB) (hHull C hRC hHC) hIndI
    (fun _ hx => closedNeighborsIn_subset_supportHull G (mem_inter.mp hx).2)
    (fun _ hx => closedNeighborsIn_subset_supportHull G (mem_inter.mp hx).2)
    (fun x hx => hdegreeL x (hIF hx))

#print axioms pair_dist_two_of_large_independent_set
#print axioms private_common_middles_le_three
#print axioms two_low_supports_contradiction
#print axioms independent_remote_card_bound

end Graph189IndependentRemotes
