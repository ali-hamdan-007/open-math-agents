import Graph189DegreeTwoOuter

namespace Graph189DegreeTwoAdjacent
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Near saturation, both neighbors miss one middle-layer vertex and the two
remote classes partition the far layer. This excludes order above three times
the second-smallest degree. -/
theorem order_le_three_sigma_of_degree_two (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b}) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree := by
  classical
  by_contra! hn
  have := h.nonempty
  let s := G.secondSmallestDegree
  change 3 * s < Fintype.card V at hn
  change 3 ≤ s at hs
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have cap (u : V) : (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s :=
    distance_two_cap s hσ u
  have ds (x y : V) : G.dist x y ≤ 3 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := y)).trans hd
  have anchors {u : V} (hu : G.Adj z u) : u = a ∨ u = b := by
    simpa [hZ] using (G.mem_neighborFinset z u).mpr hu
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hh := ds z x
    have hr : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases hr with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · have hu := anchors (dist_eq_one_iff_adj.mp h1)
      exact hu.elim (fun e => Or.inr (Or.inl e)) (fun e => Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mW x).mpr h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mR x).mpr h3))))
  have univ_eq : insert z (({a,b} : Finset V) ∪ W ∪ R) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton,Finset.mem_univ,iff_true]
    have hx := all x
    tauto
  have h₁ := Finset.card_insert_le z (({a,b} : Finset V) ∪ W ∪ R)
  rw [univ_eq,Finset.card_univ] at h₁
  have h₂ := Finset.card_union_le (({a,b} : Finset V) ∪ W) R
  have h₃ := Finset.card_union_le ({a,b} : Finset V) W
  rw [Finset.card_pair hne] at h₃
  have hN : Fintype.card V ≤ W.card + R.card + 3 := by omega
  have hWcap : W.card ≤ s := cap z
  have hRlarge : 2 * s - 2 ≤ R.card := by omega
  have reachW {r : V} (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hadj⟩ := split_three h ((mR r).mp hr)
    exact ⟨w,(mW w).mpr hw,hadj⟩
  have reachAnchor {w : V} (hw : w ∈ W) : G.Adj a w ∨ G.Adj b w := by
    obtain ⟨u,hu,hadj⟩ := split_two h ((mW w).mp hw)
    rcases anchors hu with e | e
    · exact Or.inl (e ▸ hadj)
    · exact Or.inr (e ▸ hadj)
  have remoteNo {u r : V} (hu : G.Adj z u) (hr : r ∈ R) : ¬ G.Adj u r := by
    intro hadj
    have ht := h.dist_triangle (u := z) (v := u) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hadj] at ht
    omega
  have remoteTwo {u r w : V} (hu : G.Adj z u) (hr : r ∈ R) (huw : G.Adj u w)
      (hwr : G.Adj w r) : G.dist u r = 2 := by
    have hne : u ≠ r := by
      intro e
      have hh := (mR r).mp hr
      rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
      contradiction
    exact two_edges huw hwr hne (remoteNo hu hr)
  let Da := R.filter (fun r => G.dist a r = 2)
  let Db := R.filter (fun r => G.dist b r = 2)
  let Ma := W.filter (fun w => ¬ G.Adj a w)
  let Mb := W.filter (fun w => ¬ G.Adj b w)
  have lim (u v : V) (huv : G.Adj u v) (hu : G.Adj z u)
      (hav : ∀ w ∈ W, G.Adj u w ∨ G.Adj v w) :
      (R.filter (fun r => G.dist u r = 2)).card + (W.filter (fun w => ¬ G.Adj u w)).card ≤ s ∧
        1 ≤ (W.filter (fun w => ¬ G.Adj u w)).card := by
    let D := R.filter (fun r => G.dist u r = 2)
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hsub : D ∪ M ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hx with hd' | hm
      · exact (Finset.mem_filter.mp hd').2
      · obtain ⟨hxW,hn⟩ := Finset.mem_filter.mp hm
        have hne : u ≠ x := by
          intro e
          have hh := (mW x).mp hxW
          rw [← e,dist_eq_one_iff_adj.mpr hu] at hh
          contradiction
        exact two_edges huv ((hav x hxW).resolve_left hn) hne hn
    have hdis : Disjoint D M := by
      refine Finset.disjoint_left.mpr ?_
      intro x hx hy
      have hx' := (mR x).mp (Finset.mem_filter.mp hx).1
      have hy' := (mW x).mp (Finset.mem_filter.mp hy).1
      omega
    have hl := (Finset.card_le_card hsub).trans (cap u)
    rw [Finset.card_union_of_disjoint hdis] at hl
    refine ⟨hl,?_⟩
    by_contra! hg
    change M.card < 1 at hg
    have zero : M = ∅ := Finset.card_eq_zero.mp (by omega)
    have funiv : R ⊆ D := by
      intro r hr
      obtain ⟨w,hw,hwr⟩ := reachW hr
      have huw : G.Adj u w := by
        by_contra hn
        have hm : w ∈ M := Finset.mem_filter.mpr ⟨hw,hn⟩
        simp [zero] at hm
      exact Finset.mem_filter.mpr ⟨hr,remoteTwo hu hr huw hwr⟩
    have he := Finset.card_le_card funiv
    omega
  have limNon (u v p : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (hne : u ≠ v) (hnuv : ¬ G.Adj u v) (hpW : p ∈ W)
      (hmiss : ∀ w ∈ W, G.Adj u w ↔ w ≠ p) :
      (R.filter (fun r => G.dist u r = 2)).card + (W.filter (fun w => ¬ G.Adj u w)).card ≤ s ∧
        1 ≤ (W.filter (fun w => ¬ G.Adj u w)).card := by
    let D := R.filter (fun r => G.dist u r = 2)
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hM : M = {p} := by
      ext x
      constructor
      · intro hmem
        obtain ⟨hx,hx'⟩ := Finset.mem_filter.mp hmem
        by_contra hn
        exact hx' ((hmiss x hx).mpr (by simpa using hn))
      · intro he
        have hx : x = p := by simpa using he
        subst x
        exact Finset.mem_filter.mpr ⟨hpW,fun hh => (hmiss p hpW).mp hh rfl⟩
    have hvD : v ∉ D := by
      intro hmem
      have hm := (mR v).mp (Finset.mem_filter.mp hmem).1
      rw [dist_eq_one_iff_adj.mpr hv] at hm
      contradiction
    have hsub : insert v D ⊆ Finset.univ.filter (fun w => G.dist u w = 2) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with e | hmem
      · subst x
        simp [two_edges hu.symm hv hne hnuv]
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hmem).2⟩
    have hbound := (Finset.card_le_card hsub).trans (cap u)
    rw [Finset.card_insert_of_notMem hvD] at hbound
    change D.card + M.card ≤ s ∧ 1 ≤ M.card
    simpa [hM] using hbound
  obtain ⟨⟨la,ha⟩,⟨lb,hb⟩⟩ :
      (Da.card + Ma.card ≤ s ∧ 1 ≤ Ma.card) ∧
      (Db.card + Mb.card ≤ s ∧ 1 ≤ Mb.card) := by
    by_cases hab : G.Adj a b
    · exact ⟨lim a b hab az (fun _ hx => reachAnchor hx),
        lim b a hab.symm bz (fun _ hx => (reachAnchor hx).symm)⟩
    · have hl := large_nonadjacent_layout h hd hσ (by exact hs) (by change 2*s+4 ≤ _; omega)
        z a b hne hZ hab
      obtain ⟨_,_,_,_,_,p,hp,q,hq,_,hap,hbq,_,_⟩ := hl
      exact ⟨limNon a b p az bz hne hab hp hap,
        limNon b a q bz az hne.symm (fun e => hab e.symm) hq hbq⟩
  have coverR : Da ∪ Db = R := by
    apply Finset.Subset.antisymm (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    intro r hr
    obtain ⟨w,hw,hwr⟩ := reachW hr
    apply Finset.mem_union.mpr
    exact (reachAnchor hw).imp
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo az hr he hwr⟩)
      (fun he => Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr he hwr⟩)
  have hsum := Finset.card_union_le Da Db
  rw [coverR] at hsum
  have hDa : Da.card = s - 1 := by omega
  have hDb : Db.card = s - 1 := by omega
  have hW : W.card = s := by omega
  have hMa : Ma.card = 1 := by omega
  have hMb : Mb.card = 1 := by omega
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hMa
  obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hMb
  have hpM : p ∈ Ma := by simp [hp]
  have hqM : q ∈ Mb := by simp [hq]
  obtain ⟨hpW,hpa⟩ := Finset.mem_filter.mp hpM
  obtain ⟨hqW,hqb⟩ := Finset.mem_filter.mp hqM
  have hpq : p ≠ q := by
    intro e
    exact (reachAnchor hpW).elim hpa (fun he => hqb (e ▸ he))
  have hpb : G.Adj b p := (reachAnchor hpW).resolve_left hpa
  have hqa : G.Adj a q := (reachAnchor hqW).resolve_right hqb
  have hx (u : V) (hx : u ∈ W) (hn : u ≠ p) : G.Adj a u := by
    by_contra he
    have hmu : u ∈ Ma := Finset.mem_filter.mpr ⟨hx,he⟩
    exact hn (by simpa [hp] using hmu)
  have hy (u : V) (hx : u ∈ W) (hn : u ≠ q) : G.Adj b u := by
    by_contra he
    have hmu : u ∈ Mb := Finset.mem_filter.mpr ⟨hx,he⟩
    exact hn (by simpa [hq] using hmu)
  have hcExists : 0 < ((W.erase p).erase q).card := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩
    rw [Finset.card_erase_of_mem hq',Finset.card_erase_of_mem hpW,hW]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hcExists
  have hcq : c ≠ q := Finset.ne_of_mem_erase hc
  have hcp : c ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcW : c ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hca := hx c hcW hcp
  have hcb := hy c hcW hcq
  have ddis : Disjoint Da Db := by
    by_contra hn
    have hh := Finset.card_union_add_card_inter Da Db
    rw [coverR,hDa,hDb] at hh
    have hpos : 0 < (Da ∩ Db).card := by
      have hh := Finset.disjoint_iff_inter_eq_empty.not.mp hn
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hh)
    omega
  have noRemote (r : V) (hr : r ∈ R) : ¬ G.Adj c r := by
    intro he
    have ha : r ∈ Da := Finset.mem_filter.mpr ⟨hr,remoteTwo az hr hca he⟩
    have hb : r ∈ Db := Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr hcb he⟩
    exact Finset.disjoint_left.mp ddis ha hb
  have layer_via {r : V} (hr : r ∈ R) (hn : r ∉ Da) : G.Adj p r := by
    obtain ⟨w,hw,hwr⟩ := reachW hr
    by_cases hwP : w = p
    · exact hwP ▸ hwr
    · exact (hn (Finset.mem_filter.mpr ⟨hr,remoteTwo az hr (hx w hw hwP) hwr⟩)).elim
  have layer_via' {r : V} (hr : r ∈ R) (hn : r ∉ Db) : G.Adj q r := by
    obtain ⟨w,hw,hwr⟩ := reachW hr
    by_cases hwQ : w = q
    · exact hwQ ▸ hwr
    · exact (hn (Finset.mem_filter.mpr ⟨hr,remoteTwo bz hr (hy w hw hwQ) hwr⟩)).elim
  have acrossP (r : V) (hr : r ∈ Db) : G.Adj p r :=
    layer_via (Finset.mem_filter.mp hr).1 (fun he => Finset.disjoint_left.mp ddis he hr)
  have acrossQ (r : V) (hr : r ∈ Da) : G.Adj q r :=
    layer_via' (Finset.mem_filter.mp hr).1 (fun he => Finset.disjoint_left.mp ddis hr he)
  have hz2 : G.dist c z = 2 := by rw [dist_comm]; exact (mW c).mp hcW
  have hzR : z ∉ R := by intro hz; have hh := (mR z).mp hz; simp at hh
  have cDistance {v r : V} (hcv : G.Adj c v) (hvr : G.Adj v r) (hr : r ∈ R) :
      G.dist c r = 2 := by
    have hne : c ≠ r := by
      intro e
      have hl := (mW c).mp hcW
      have hh := (mR r).mp hr
      rw [e] at hl
      omega
    exact two_edges hcv hvr hne (noRemote r hr)
  have impossibleBoth (hP : G.Adj c p) (hQ : G.Adj c q) : False := by
    have hsub : insert z R ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
      intro x hh
      rcases Finset.mem_insert.mp hh with e | hr
      · subst x; simp [hz2]
      · have h' := hr
        rw [← coverR] at h'
        rcases Finset.mem_union.mp h' with ha | hb
        · simp [cDistance hQ (acrossQ x ha) hr]
        · simp [cDistance hP (acrossP x hb) hr]
    have hcap := (Finset.card_le_card hsub).trans (cap c)
    rw [Finset.card_insert_of_notMem hzR] at hcap
    omega
  have excessive {v w : V} {D : Finset V} (hcv : G.Adj c v) (hwW : w ∈ W)
      (hw2 : G.dist c w = 2) (hD : D.card = s - 1) (hDR : D ⊆ R)
      (hVR : ∀ r ∈ D, G.Adj v r) : False := by
    have hwD : w ∉ D := by
      intro he
      have hw' := (mW w).mp hwW
      have hw'' := (mR w).mp (hDR he)
      omega
    have hzD : z ∉ insert w D := by
      intro he
      rcases Finset.mem_insert.mp he with e | h
      · have hh := (mW w).mp hwW
        simp [← e] at hh
      · exact hzR (hDR h)
    have hsub : insert z (insert w D) ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
      intro x he
      rcases Finset.mem_insert.mp he with e | hm
      · subst x; simp [hz2]
      · rcases Finset.mem_insert.mp hm with e | hr
        · subst x; simp [hw2]
        · simp [cDistance hcv (hVR x hr) (hDR hr)]
    have hle := (Finset.card_le_card hsub).trans (cap c)
    rw [Finset.card_insert_of_notMem hzD,Finset.card_insert_of_notMem hwD,hD] at hle
    omega
  have noP : ¬ G.Adj c p := by
    intro hadj
    have hno : ¬ G.Adj c q := fun h => impossibleBoth hadj h
    exact excessive hadj hqW (two_edges hca.symm hqa hcq hno) hDb
      (Finset.filter_subset _ _) acrossP
  have noQ : ¬ G.Adj c q := by
    intro hadj
    exact excessive hadj hpW (two_edges hcb.symm hpb hcp noP) hDa
      (Finset.filter_subset _ _) acrossQ
  let S := ((W.erase p).erase q).erase c
  have hbound : G.neighborFinset c ⊆ ({a,b} : Finset V) ∪ S := by
    intro x hx
    have he := (G.mem_neighborFinset c x).mp hx
    rcases all x with e | e | e | hw | hr
    · subst x
      have hcz := (mW c).mp hcW
      rw [dist_eq_one_iff_adj.mpr he.symm] at hcz
      contradiction
    · exact Finset.mem_union_left _ (by simp [e])
    · exact Finset.mem_union_left _ (by simp [e])
    · have hxp : x ≠ p := fun eq => noP (eq ▸ he)
      have hxq : x ≠ q := fun eq => noQ (eq ▸ he)
      have hxc : x ≠ c := (G.ne_of_adj he).symm
      exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨hxc,Finset.mem_erase.mpr ⟨hxq,Finset.mem_erase.mpr ⟨hxp,hw⟩⟩⟩)
    · exact (noRemote x hr he).elim
  have hS : S.card = s - 3 := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩
    dsimp [S]
    rw [Finset.card_erase_of_mem hc,Finset.card_erase_of_mem hq',
      Finset.card_erase_of_mem hpW,hW]
    omega
  have hlow := (Finset.card_le_card hbound).trans (Finset.card_union_le _ _)
  rw [Finset.card_pair hne,hS] at hlow
  have hcNe : c ≠ z := by intro he; have hh := (mW c).mp hcW; simp [he] at hh
  have hhigh : s ≤ G.degree c := (Graph189Bipartite.degree_pair (G := G) c z hcNe).resolve_right (by
    change ¬ s ≤ G.degree z; omega)
  change G.degree c ≤ 2 + (s - 3) at hlow
  omega

/-- The upper bound applies as soon as the graph has a vertex of degree two. -/
theorem order_le_three_sigma (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree) (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree := by
  have hz' : (G.neighborFinset z).card = 2 := hz
  obtain ⟨a,b,hne,hpair⟩ := Finset.card_eq_two.mp hz'
  exact order_le_three_sigma_of_degree_two h hd hσ hs z a b hne hpair

/-- For second-smallest degree three the bound excludes every order above nine. -/
theorem order_le_nine_of_sigma_three (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 3)
    (z : V) (hz : G.degree z = 2) :
    Fintype.card V ≤ 9 := by
  simpa [hs] using order_le_three_sigma h hd hσ (by omega) z hz

#print axioms order_le_three_sigma
#print axioms order_le_nine_of_sigma_three
end Graph189DegreeTwoAdjacent
