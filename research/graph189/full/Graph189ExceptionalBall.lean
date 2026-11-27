import Graph189DistanceLayers

namespace Graph189ExceptionalBall

open SimpleGraph Graph189LowDegreeTwo

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The radius-two ball around c with z removed, as an inducing set. -/
def deletedBall (G : SimpleGraph V) (c z : V) : Set V :=
  {v | G.dist c v ≤ 2 ∧ v ≠ z}

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem neighbor_in_ball {c x : V} (h : G.Adj c x) :
    G.dist c x ≤ 2 := by
  rw [dist_eq_one_iff_adj.mpr h]
  decide

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem two_adj_in_ball (hc : G.Connected) {c a x : V}
    (ha : G.Adj c a) (hx : G.Adj a x) :
    G.dist c x ≤ 2 := by
  have h := hc.dist_triangle (u := c) (v := a) (w := x)
  rwa [dist_eq_one_iff_adj.mpr ha, dist_eq_one_iff_adj.mpr hx] at h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem induce_reach {F : Set V} {x y : F} (h : G.Adj (x : V) (y : V)) :
    (G.induce F).Reachable x y :=
  (induce_adj.mpr h).reachable

/-- If z has a smaller degree than k and every other vertex has degree at
least k, its radius-two ball stays connected when z is deleted. Only the
distance-two bound at z is needed. -/
theorem center_ball_connected [Nontrivial V] (hc : G.Connected) {k : ℕ} {z : V}
    (hdeg : ∀ v, v ≠ z → k ≤ G.degree v)
    (hlow : G.degree z < k)
    (hcap : (Finset.univ.filter (fun v => G.dist z v = 2)).card ≤ k) :
    (G.induce (deletedBall G z z)).Connected := by
  classical
  let S := deletedBall G z z
  let H := G.induce S
  let U := Finset.univ.filter (fun v => v ∈ S)
  have hU : U.card ≤ G.degree z + k := by
    let D := Finset.univ.filter (fun v => G.dist z v = 2)
    have sub : U ⊆ G.neighborFinset z ∪ D := by
      intro v hv
      have hvs : v ∈ S := Finset.mem_filter.mp hv |>.2
      have hp : G.dist z v ≠ 0 := fun e =>
        hvs.2 ((hc.preconnected z v).dist_eq_zero_iff.mp e).symm
      by_cases h : G.dist z v = 1
      · exact Finset.mem_union_left _ ((G.mem_neighborFinset z v).mpr
          (dist_eq_one_iff_adj.mp h))
      · have he : G.dist z v = 2 := by have := hvs.1; omega
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    have le := Finset.card_le_card sub
    have le' := Finset.card_union_le (G.neighborFinset z) D
    rw [G.card_neighborFinset_eq_degree] at le'
    change D.card ≤ k at hcap
    omega
  have anchor (a : V) (ha : G.Adj z a) : a ∈ S :=
    ⟨neighbor_in_ball ha, ha.ne.symm⟩
  have onto (v : S) : ∃ (a : V) (ha : G.Adj z a), H.Reachable ⟨a, anchor a ha⟩ v := by
    have hp : G.dist z (v : V) ≠ 0 := fun e =>
      v.property.2 ((hc.preconnected z v).dist_eq_zero_iff.mp e).symm
    by_cases h : G.dist z (v : V) = 1
    · exact ⟨v, dist_eq_one_iff_adj.mp h, Reachable.refl v⟩
    · have he : G.dist z (v : V) = 2 := by have := v.property.1; omega
      obtain ⟨a,ha,hav⟩ := split_two hc he
      exact ⟨a,ha,induce_reach hav⟩
  let K (a : V) := insert a ((G.neighborFinset a).erase z)
  have Kcard (a : V) (ha : G.Adj z a) : (K a).card = G.degree a := by
    have hn : a ∉ (G.neighborFinset a).erase z := by
      simp [G.mem_neighborFinset]
    dsimp [K]
    rw [Finset.card_insert_of_notMem hn,
      Finset.card_erase_add_one ((G.mem_neighborFinset a z).mpr ha.symm),
      G.card_neighborFinset_eq_degree]
  have Kinside (a : V) (ha : G.Adj z a) {v : V} (hv : v ∈ K a) : v ∈ S := by
    rcases Finset.mem_insert.mp hv with h | h
    · subst v
      exact anchor a ha
    · obtain ⟨hne, hn⟩ := Finset.mem_erase.mp h
      exact ⟨two_adj_in_ball hc ha ((G.mem_neighborFinset a v).mp hn), hne⟩
  have Kreach (a : V) (ha : G.Adj z a) {v : V} (hv : v ∈ K a) :
      H.Reachable ⟨a, anchor a ha⟩ ⟨v, Kinside a ha hv⟩ := by
    rcases Finset.mem_insert.mp hv with h | h
    · subst v
      exact Reachable.refl _
    · exact induce_reach ((G.mem_neighborFinset a v).mp (Finset.mem_erase.mp h).2)
  have link (a b : V) (ha : G.Adj z a) (hb : G.Adj z b) :
      H.Reachable ⟨a, anchor a ha⟩ ⟨b, anchor b hb⟩ := by
    by_contra h
    have hd : Disjoint (K a) (K b) := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv hw
      exact h ((Kreach a ha hv).trans (Kreach b hb hw).symm)
    have hu : K a ∪ K b ⊆ U := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_union.mp hv).elim
        (Kinside a ha) (Kinside b hb)⟩
    have hsum := Finset.card_le_card hu
    rw [Finset.card_union_of_disjoint hd,Kcard a ha,Kcard b hb] at hsum
    have ha' := hdeg a ha.ne.symm
    have hb' := hdeg b hb.ne.symm
    omega
  obtain ⟨a,ha⟩ := hc.preconnected.exists_adj_of_nontrivial z
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨a, anchor a ha⟩, fun v => ?_⟩
  obtain ⟨b,hb,hbv⟩ := onto v
  exact (link a b ha hb).trans hbv


/-- If deleting z disconnects a ball centered elsewhere, the degree of its
center plus the degree floor outside z is bounded by z's degree and
distance-two count. -/
theorem off_center_ball_count (hc : G.Connected) {k : ℕ} {c z : V}
    (hcz : c ≠ z) (hdeg : ∀ v, v ≠ z → k ≤ G.degree v)
    (hcut : ¬ (G.induce (deletedBall G c z)).Connected) :
    G.degree c + k ≤ G.degree z + (Finset.univ.filter (fun v => G.dist z v = 2)).card := by
  classical
  let S := deletedBall G c z
  let H := G.induce S
  let root : S := ⟨c, by simp [S, deletedBall, hcz]⟩
  have hsome : ∃ y : S, ¬ H.Reachable root y := by
    by_contra hn
    push Not at hn
    exact hcut ((connected_iff_exists_forall_reachable H).mpr ⟨root, hn⟩)
  have detached {y : S} (hy : ¬ H.Reachable root y) :
      G.Adj c z ∧ G.Adj z (y : V) ∧ ¬ G.Adj c (y : V) := by
    have hne : c ≠ (y : V) := by
      intro hp
      exact hy ((Subtype.ext hp : root = y) ▸ Reachable.refl root)
    have hno : ¬ G.Adj c (y : V) := fun he => hy (induce_reach he)
    have hd0 : G.dist c (y : V) ≠ 0 := fun e =>
      hne ((hc.preconnected c y).dist_eq_zero_iff.mp e)
    have hd1 : G.dist c (y : V) ≠ 1 := fun e => hno (dist_eq_one_iff_adj.mp e)
    have hd2 : G.dist c (y : V) = 2 := by have := y.property.1; omega
    obtain ⟨w,hw,hyw⟩ := split_two hc hd2
    by_cases hwz : w = z
    · subst w
      exact ⟨hw,hyw,hno⟩
    · let mid : S := ⟨w, neighbor_in_ball hw, hwz⟩
      exact False.elim (hy ((induce_reach (y := mid) hw).trans (induce_reach hyw)))
  obtain ⟨y,hy⟩ := hsome
  obtain ⟨hczadj,hzy,hcy⟩ := detached hy
  let I := (G.neighborFinset c).erase z \ G.neighborFinset z
  let D := (G.neighborFinset z).erase c \ G.neighborFinset c
  have hIy : (y : V) ∈ D := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_,(G.mem_neighborFinset z y).mpr hzy⟩, ?_⟩
    · intro e
      exact hy ((Subtype.ext e.symm : root = y) ▸ Reachable.refl root)
    · exact fun h => hcy ((G.mem_neighborFinset c y).mp h)
  have hsize : I.card + G.degree z = D.card + G.degree c := by
    have hi := Finset.card_sdiff_add_card_inter ((G.neighborFinset c).erase z) (G.neighborFinset z)
    have hd := Finset.card_sdiff_add_card_inter ((G.neighborFinset z).erase c) (G.neighborFinset c)
    have eqI : (G.neighborFinset c).erase z ∩ G.neighborFinset z =
        G.neighborFinset c ∩ G.neighborFinset z := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
      exact ⟨fun ⟨⟨_,hc'⟩,hz'⟩ => ⟨hc',hz'⟩, fun ⟨hc',hz'⟩ => ⟨⟨hz'.ne.symm,hc'⟩,hz'⟩⟩
    have eqD : (G.neighborFinset z).erase c ∩ G.neighborFinset c =
        G.neighborFinset c ∩ G.neighborFinset z := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_erase, G.mem_neighborFinset]
      exact ⟨fun ⟨⟨_,hz'⟩,hc'⟩ => ⟨hc',hz'⟩, fun ⟨hc',hz'⟩ => ⟨⟨hc'.ne.symm,hz'⟩,hc'⟩⟩
    rw [eqI] at hi
    rw [eqD] at hd
    have eI := Finset.card_erase_add_one ((G.mem_neighborFinset c z).mpr hczadj)
    have eD := Finset.card_erase_add_one ((G.mem_neighborFinset z c).mpr hczadj.symm)
    rw [G.card_neighborFinset_eq_degree] at eI eD
    change I.card + (G.neighborFinset c ∩ G.neighborFinset z).card =
      ((G.neighborFinset c).erase z).card at hi
    change D.card + (G.neighborFinset c ∩ G.neighborFinset z).card =
      ((G.neighborFinset z).erase c).card at hd
    omega
  let F := (G.neighborFinset y).filter (fun v => G.dist c v ≤ 2)
  let J := (G.neighborFinset y).filter (fun v => ¬ G.dist c v ≤ 2)
  have hF : F.card ≤ D.card := by
    have hsub : F ⊆ insert z (D.erase y) := by
      intro v hv
      obtain ⟨hvy, hdv⟩ := Finset.mem_filter.mp hv
      by_cases hvz : v = z
      · exact Finset.mem_insert.mpr (Or.inl hvz)
      · let x : S := ⟨v, hdv, hvz⟩
        have hadj := (G.mem_neighborFinset y v).mp hvy
        have hreach : ¬ H.Reachable root x := fun hx =>
          hy (hx.trans (induce_reach hadj.symm))
        obtain ⟨_,hzx,hcx⟩ := detached hreach
        have hxc : v ≠ c := by
          intro e
          exact hreach ((Subtype.ext e.symm : root = x) ▸ Reachable.refl root)
        have hvD : v ∈ D := Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨hxc,(G.mem_neighborFinset z v).mpr hzx⟩,
            fun he => hcx ((G.mem_neighborFinset c v).mp he)⟩
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hadj.ne.symm,hvD⟩))
    have hcard := Finset.card_le_card hsub
    have herase := Finset.card_erase_add_one hIy
    have hcard' := Finset.card_insert_le z (D.erase y)
    omega
  have hdegJ : k ≤ F.card + J.card := by
    have heq := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset y) (fun v => G.dist c v ≤ 2)
    rw [G.card_neighborFinset_eq_degree] at heq
    change F.card + J.card = G.degree y at heq
    exact heq ▸ hdeg y y.property.2
  let L := Finset.univ.filter (fun v => G.dist z v = 2)
  have hiL : I ⊆ L := by
    intro v hv
    obtain ⟨hi,hno⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨hvz,hvI⟩ := Finset.mem_erase.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      two_edges hczadj.symm ((G.mem_neighborFinset c v).mp hvI) hvz.symm
        (fun he => hno ((G.mem_neighborFinset z v).mpr he))⟩
  have hjL : J ⊆ L := by
    intro v hv
    obtain ⟨hj,hfar⟩ := Finset.mem_filter.mp hv
    have hvz : v ≠ z := fun e => hfar (e ▸ neighbor_in_ball hczadj)
    have hzn : ¬ G.Adj z v := fun he => hfar (two_adj_in_ball hc hczadj he)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      two_edges hzy ((G.mem_neighborFinset y v).mp hj) hvz.symm hzn⟩
  have hIJ : Disjoint I J := by
    refine Finset.disjoint_left.mpr ?_
    intro v hi hj
    have hc' := (G.mem_neighborFinset c v).mp (Finset.mem_erase.mp (Finset.mem_sdiff.mp hi).1).2
    exact (Finset.mem_filter.mp hj).2 (neighbor_in_ball hc')
  have hsum := Finset.card_le_card (Finset.union_subset hiL hjL)
  rw [Finset.card_union_of_disjoint hIJ] at hsum
  change G.degree c + k ≤ G.degree z + L.card
  omega

/-- The unique vertex of degree below k cannot disconnect any induced
radius-two ball, provided only its own second neighborhood has size at
most k. -/
theorem all_balls_connected_after_deleting_low [Nontrivial V]
    (hc : G.Connected) {k : ℕ} {z : V}
    (hdeg : ∀ v, v ≠ z → k ≤ G.degree v) (hlow : G.degree z < k)
    (hcap : (Finset.univ.filter (fun v => G.dist z v = 2)).card ≤ k) (c : V) :
    (G.induce (deletedBall G c z)).Connected := by
  by_cases hcz : c = z
  · subst c
    exact center_ball_connected hc hdeg hlow hcap
  · by_contra hcut
    have hcount := off_center_ball_count hc hcz hdeg hcut
    have hhigh := hdeg c hcz
    omega

/-- A low-degree neighbor z of c lies in the same component of the
deleted ball around c as another neighbor of c, if z has degree at least
two. Thus z cannot be the sole anchor in a split component. -/
theorem low_anchor_has_other_anchor (hc : G.Connected) {k : ℕ} {c z : V}
    (hcz : G.Adj c z) (hdeg : ∀ v, v ≠ z → k ≤ G.degree v)
    (hpos : 2 ≤ G.degree z) (hlow : G.degree z < k)
    (hcap : (Finset.univ.filter (fun v => G.dist z v = 2)).card ≤ k) :
    ∃ (a : V) (ha : G.Adj c a), a ≠ z ∧
      (G.induce (deletedBall G c c)).Reachable
        ⟨z, neighbor_in_ball hcz, hcz.ne.symm⟩
        ⟨a, neighbor_in_ball ha, ha.ne.symm⟩ := by
  classical
  let S := deletedBall G c c
  let H := G.induce S
  let root : S := ⟨z, neighbor_in_ball hcz, hcz.ne.symm⟩
  let T := deletedBall G c z
  let K := G.induce T
  let endpoint : T := ⟨c, by simp [T, deletedBall, hcz.ne]⟩
  have hK : K.Connected := by
    let : Nontrivial V := ⟨⟨c,z,hcz.ne⟩⟩
    exact all_balls_connected_after_deleting_low hc hdeg hlow hcap c
  have hpos' : 0 < ((G.neighborFinset z).erase c).card := by
    have h := Finset.card_erase_add_one ((G.mem_neighborFinset z c).mpr hcz.symm)
    rw [G.card_neighborFinset_eq_degree] at h
    omega
  obtain ⟨p,hp⟩ := Finset.card_pos.mp hpos' 
  obtain ⟨hpc,hpz⟩ := Finset.mem_erase.mp hp
  have hzp := (G.mem_neighborFinset z p).mp hpz
  let start : T := ⟨p, two_adj_in_ball hc hcz hzp, hzp.ne.symm⟩
  by_contra hno
  let side (v : T) : Prop :=
    ∃ hv : (v : V) ≠ c, H.Reachable root ⟨v, v.property.1, hv⟩
  have closed {u v : T} (h : K.Adj u v) (hu : side u) : side v := by
    obtain ⟨huc,hur⟩ := hu
    have huv := induce_adj.mp h
    by_cases hvc : (v : V) = c
    · have hua : G.Adj c (u : V) := hvc ▸ huv.symm
      exact False.elim (hno ⟨u,hua,u.property.2,hur⟩)
    · exact ⟨hvc,hur.trans (induce_reach huv)⟩
  have preserve {u v : T} (w : K.Walk u v) (hu : side u) : side v := by
    induction w with
    | nil => exact hu
    | cons h _ ih => exact ih (closed h hu)
  obtain ⟨w⟩ := hK.preconnected start endpoint
  have hs : side start := ⟨hpc,induce_reach hzp⟩
  exact (preserve w hs).choose rfl

end Graph189ExceptionalBall

#print axioms Graph189ExceptionalBall.center_ball_connected
#print axioms Graph189ExceptionalBall.off_center_ball_count
#print axioms Graph189ExceptionalBall.all_balls_connected_after_deleting_low

#print axioms Graph189ExceptionalBall.low_anchor_has_other_anchor
