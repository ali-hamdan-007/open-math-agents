import Graph189IndependentRemotes

namespace Graph189ArbitraryTripleIndependence

open SimpleGraph Finset Graph189SaturatedDistance Graph189IndependentRemotes

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- If twice the minimum degree exceeds the independent complement, each
distinct pair shares an induced-layer neighbor and is at full-graph distance two. -/
theorem pair_dist_two_of_degree_overlap {F I : Finset V} {d : ℕ}
    (hoverlap : (F \ I).card < 2 * d)
    (hdegree : ∀ x ∈ I, d ≤ (neighborsIn G F x).card)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    {x y : V} (hx : x ∈ I) (hy : y ∈ I) (hne : x ≠ y) :
    ∃ z ∈ F \ I, G.Adj x z ∧ G.Adj y z ∧ G.dist x y = 2 := by
  have hsub (v : V) (hv : v ∈ I) : neighborsIn G F v ⊆ F \ I := by
    intro z hz
    obtain ⟨hzF, hvz⟩ := mem_filter.mp hz
    exact mem_sdiff.mpr ⟨hzF, fun hzI => hind v hv z hzI hvz⟩
  have hu := card_le_card (union_subset (hsub x hx) (hsub y hy))
  have hinter := card_inter_add_card_union (neighborsIn G F x) (neighborsIn G F y)
  have hpos : 0 < ((neighborsIn G F x) ∩ (neighborsIn G F y)).card := by
    have := hdegree x hx
    have := hdegree y hy
    omega
  obtain ⟨z, hz⟩ := card_pos.mp hpos
  obtain ⟨hzx, hzy⟩ := mem_inter.mp hz
  have hxz := (mem_filter.mp hzx).2
  have hyz := (mem_filter.mp hzy).2
  exact ⟨z, hsub x hx hzx, hxz, hyz,
    dist_two_of_common_neighbor G hne (hind x hx y hy) hxz hyz⟩

omit [DecidableRel G.Adj] in
/-- The other independent vertices, the common middles and the anchor
occupy disjoint sets of positive even-distance slots. -/
theorem common_budget_of_independent_remotes [Fintype V]
    {F I : Finset V} {k : ℕ} (J : PrivateGeometry G F)
    (hIF : I ⊆ F) {x : V} (hx : x ∈ I) (hxJ : G.Adj x J.privateVertex)
    (hpair : ∀ y ∈ I.erase x, G.dist x y = 2)
    (hcap : (evenBall G x).card ≤ k + 1) :
    I.card + J.common.card ≤ k := by
  have hfixed (v : V) (hv : v ∈ insert J.anchor J.common) : G.dist x v = 2 := by
    rcases mem_insert.mp hv with rfl | hv
    · have hne : x ≠ J.anchor := fun he => J.anchorNotRemote (he ▸ hIF hx)
      exact dist_two_of_common_neighbor G hne (J.remotesMissAnchor x (hIF hx))
        hxJ J.privateAnchor.symm
    · have hne : x ≠ v := fun he =>
        (Finset.disjoint_left.mp J.commonNotRemote hv) (he ▸ hIF hx)
      exact dist_two_of_common_neighbor G hne (J.remotesMissCommon x (hIF hx) v hv)
        hxJ (J.privateCommon v hv).symm
  have hdis : Disjoint (I.erase x) (insert J.anchor J.common) := by
    apply Finset.disjoint_left.mpr
    intro v hv hf
    have hvF := hIF (mem_erase.mp hv).2
    rcases mem_insert.mp hf with rfl | hf
    · exact J.anchorNotRemote hvF
    · exact (Finset.disjoint_left.mp J.commonNotRemote hf) hvF
  have h := card_add_le_of_disjoint_distance_two G hpair hfixed hdis hcap
  rw [card_insert_of_notMem J.anchorNotCommon] at h
  have hErase := card_erase_add_one hx
  omega

/-- The closed neighborhood of a member of the independent set leaves
room in the support hull only for the other independent support members. -/
theorem support_inter_card_le_common_add_one
    {F L I : Finset V} {k : ℕ} (J : PrivateGeometry G F)
    (hR : (neighborsIn G L J.privateVertex).card ≤ k - 3)
    (hH : (supportHull G L J.privateVertex).card ≤
      (neighborsIn G L J.privateVertex).card + J.common.card + 1)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hdegree : ∀ x ∈ I, k - 2 ≤ (closedNeighborsIn G L x).card) :
    (I ∩ neighborsIn G L J.privateVertex).card ≤ J.common.card + 1 := by
  let R := neighborsIn G L J.privateVertex
  change (I ∩ R).card ≤ _
  by_cases he : (I ∩ R).Nonempty
  · obtain ⟨x, hx⟩ := he
    obtain ⟨hxI, hxR⟩ := mem_inter.mp hx
    have hsub : (I ∩ R).erase x ⊆ supportHull G L J.privateVertex := by
      intro y hy
      exact support_subset_supportHull G L J.privateVertex
        (mem_inter.mp (mem_erase.mp hy).2).2
    have hdis : Disjoint ((I ∩ R).erase x) (closedNeighborsIn G L x) := by
      apply Finset.disjoint_left.mpr
      intro y hy hyN
      obtain ⟨hne, hyIR⟩ := mem_erase.mp hy
      rcases (mem_filter.mp hyN).2 with hEq | hadj
      · exact hne hEq.symm
      · exact hind x hxI y (mem_inter.mp hyIR).1 hadj
    have hcard := card_le_card
      (union_subset hsub (closedNeighborsIn_subset_supportHull G hxR))
    rw [card_union_of_disjoint hdis] at hcard
    have hErase := card_erase_add_one hx
    have hClose := hdegree x hxI
    have hRPos : 0 < R.card := card_pos.mpr ⟨x, hxR⟩
    change R.card ≤ k - 3 at hR
    change (supportHull G L J.privateVertex).card ≤ R.card + J.common.card + 1 at hH
    omega
  · have hempty : I ∩ R = ∅ := by
      by_contra h
      exact he (nonempty_iff_ne_empty.mpr h)
    simp [hempty]

/-- In the overlap regime a touched private has at most (k-b) common
neighbors and its support contains at most (k-b+1) members of I. -/
theorem support_budget_of_degree_overlap [Fintype V]
    {F L I : Finset V} {d k : ℕ} (J : PrivateGeometry G F)
    (hIF : I ⊆ F) (hoverlap : (F \ I).card < 2 * d)
    (hdegreeF : ∀ x ∈ I, d ≤ (neighborsIn G F x).card)
    (hdegreeL : ∀ x ∈ I, k - 2 ≤ (closedNeighborsIn G L x).card)
    (hcap : ∀ x ∈ I, (evenBall G x).card ≤ k + 1)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hR : (neighborsIn G L J.privateVertex).card ≤ k - 3)
    (hH : (supportHull G L J.privateVertex).card ≤
      (neighborsIn G L J.privateVertex).card + J.common.card + 1) :
    (((I ∩ neighborsIn G L J.privateVertex).Nonempty) → J.common.card ≤ k - I.card) ∧
      (I ∩ neighborsIn G L J.privateVertex).card ≤ k - I.card + 1 := by
  have hCommon (he : (I ∩ neighborsIn G L J.privateVertex).Nonempty) :
      J.common.card ≤ k - I.card := by
    obtain ⟨x, hx⟩ := he
    obtain ⟨hxI, hxJ⟩ := mem_inter.mp hx
    have hpair (y : V) (hy : y ∈ I.erase x) : G.dist x y = 2 := by
      obtain ⟨hyx, hyI⟩ := mem_erase.mp hy
      obtain ⟨_, _, _, _, hd⟩ := pair_dist_two_of_degree_overlap G hoverlap
        hdegreeF hind hxI hyI hyx.symm
      exact hd
    have := common_budget_of_independent_remotes G J hIF hxI
      (mem_filter.mp hxJ).2.symm hpair (hcap x hxI)
    omega
  refine ⟨hCommon, ?_⟩
  by_cases he : (I ∩ neighborsIn G L J.privateVertex).Nonempty
  · have := support_inter_card_le_common_add_one G J hR hH hind hdegreeL
    have := hCommon he
    omega
  · have := not_lt.mp (fun hp => he (card_pos.mp hp))
    omega

/-- The fixed-triple template's order and degree conditions yield the two
alternative independence bounds directly in the original graph metric. -/
theorem fixed_triple_independence_bound [Fintype V]
    {F L I : Finset V} {k h d : ℕ} (J : Fin 4 → PrivateGeometry G F)
    (hIF : I ⊆ F) (hFL : F ⊆ L) (hOrder : 2 * F.card + 12 + 3 * h ≤ 5 * k)
    (hd : k - 3 - h ≤ d)
    (hdegreeF : ∀ x ∈ I, d ≤ (neighborsIn G F x).card)
    (hdegreeL : ∀ x ∈ I, k - 2 ≤ (closedNeighborsIn G L x).card)
    (hcap : ∀ x ∈ I, (evenBall G x).card ≤ k + 1)
    (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ G.Adj x y)
    (hcover : ∀ x ∈ I, ∃ j, G.Adj x (J j).privateVertex)
    (hR : ∀ j, (neighborsIn G L (J j).privateVertex).card ≤ k - 3)
    (hH : ∀ j, (supportHull G L (J j).privateVertex).card ≤
      (neighborsIn G L (J j).privateVertex).card + (J j).common.card + 1) :
    2 * I.card ≤ k + h ∨ 5 * I.card ≤ 4 * k + 4 := by
  by_cases hoverlap : (F \ I).card < 2 * d
  · right
    let S (j : Fin 4) := I ∩ neighborsIn G L (J j).privateVertex
    have hEach (j : Fin 4) : (S j).card ≤ k - I.card + 1 :=
      (support_budget_of_degree_overlap G (J j) hIF hoverlap hdegreeF hdegreeL
        hcap hind (hR j) (hH j)).2
    have hsub : I ⊆ univ.biUnion S := by
      intro x hx
      obtain ⟨j, hj⟩ := hcover x hx
      exact mem_biUnion.mpr
        ⟨j, mem_univ _, mem_inter.mpr ⟨hx, mem_filter.mpr ⟨hFL (hIF hx), hj.symm⟩⟩⟩
    have hCard := card_le_card hsub
    have hSum := card_biUnion_le (s := (univ : Finset (Fin 4))) (t := S)
    have hBound := sum_le_sum (s := (univ : Finset (Fin 4)))
      (fun j _ => hEach j)
    simp at hBound
    have hb : I.card ≤ 4 * (k - I.card + 1) := by omega
    by_cases hEmpty : I.Nonempty
    · obtain ⟨x, hx⟩ := hEmpty
      obtain ⟨j, hj⟩ := hcover x hx
      have hpair (y : V) (hy : y ∈ I.erase x) : G.dist x y = 2 := by
        obtain ⟨hyx, hyI⟩ := mem_erase.mp hy
        obtain ⟨_, _, _, _, hdist⟩ := pair_dist_two_of_degree_overlap G hoverlap
          hdegreeF hind hx hyI hyx.symm
        exact hdist
      have := common_budget_of_independent_remotes G (J j) hIF hx hj hpair (hcap x hx)
      omega
    · have := not_lt.mp (fun hp => hEmpty (card_pos.mp hp))
      omega
  · left
    have hSplit := card_sdiff_add_card_eq_card hIF
    omega

#print axioms pair_dist_two_of_degree_overlap
#print axioms support_budget_of_degree_overlap
#print axioms fixed_triple_independence_bound

end Graph189ArbitraryTripleIndependence
