import Graph189DegreeTwoFinalBound

namespace Graph189DegreeTwoRooted
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter Graph189DegreeTwoNearSaturation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem large_nonadjacent_layout_rooted (z : V) (h : G.Connected) (hd : ∀ x, G.dist z x ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (hn : 2 * G.secondSmallestDegree + 4 ≤ Fintype.card V)
    (a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b})
    (hab : ¬ G.Adj a b) :
    let W := Finset.univ.filter (fun v => G.dist z v = 2)
    let R := Finset.univ.filter (fun v => G.dist z v = 3)
    W.card + R.card + 3 = Fintype.card V ∧
    W.card = G.secondSmallestDegree ∧ G.secondSmallestDegree + 1 ≤ R.card ∧
      G.degree a = G.secondSmallestDegree ∧ G.degree b = G.secondSmallestDegree ∧
        ∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧
          (∀ x ∈ W, G.Adj a x ↔ x ≠ p) ∧ (∀ x ∈ W, G.Adj b x ↔ x ≠ q) ∧
          2 ≤ (R.filter (fun x => 2 < G.dist a x)).card ∧
          2 ≤ (R.filter (fun x => 2 < G.dist b x)).card := by
  classical
  have := h.nonempty
  let s := G.secondSmallestDegree
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  intro W' R'
  change W.card + R.card + 3 = Fintype.card V ∧ W.card = s ∧ s + 1 ≤ R.card ∧ _
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have mW (x) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hc : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by
      have := hd x
      omega
    rcases hc with h0 | h1 | h2 | h3
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · have hNx := (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
      simpa [hZ,or_assoc] using
        (Or.inr (Or.inl hNx) : x = z ∨ x ∈ G.neighborFinset z ∨ x ∈ W ∨ x ∈ R)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mW x).mpr h2))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mR x).mpr h3))))
  have hun : insert z (({a,b} : Finset V) ∪ W ∪ R) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton,Finset.mem_univ,iff_true]
    have hx := all x
    tauto
  have hT (x : V) (hx : x ∈ ({a,b} : Finset V)) : G.dist z x = 1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset z x).mp (hZ.symm ▸ hx))
  have hdisW : Disjoint ({a,b} : Finset V) W := by
    refine Finset.disjoint_left.mpr (fun x hx hw => ?_)
    have := hT x hx
    have := (mW x).mp hw
    omega
  have hdisR : Disjoint (({a,b} : Finset V) ∪ W) R := by
    refine Finset.disjoint_left.mpr (fun x hx hr => ?_)
    have := (mR x).mp hr
    rcases Finset.mem_union.mp hx with ht | hw
    · have := hT x ht
      omega
    · have := (mW x).mp hw
      omega
  have hzEmpty : z ∉ (({a,b} : Finset V) ∪ W ∪ R) := by
    simp [mW,mR, G.ne_of_adj hza, G.ne_of_adj hzb]
  have hL := congrArg Finset.card hun
  rw [Finset.card_insert_of_notMem hzEmpty,Finset.card_union_of_disjoint hdisR,
    Finset.card_union_of_disjoint hdisW,Finset.card_pair hne,Finset.card_univ] at hL
  have hOrder : W.card + R.card + 3 = Fintype.card V := by omega
  have hWcap : W.card ≤ s := distance_two_cap s hσ z
  have hRsize : s + 1 ≤ R.card := by change 2*s+4 ≤ Fintype.card V at hn; omega
  have reachW (r : V) (hr : r ∈ R) : ∃ w ∈ W, G.Adj w r := by
    obtain ⟨w,hw,hwr⟩ := split_three h ((mR r).mp hr)
    exact ⟨w,(mW w).mpr hw,hwr⟩
  have remoteNo {u r : V} (hu : G.Adj z u) (hr : r ∈ R) : ¬ G.Adj u r := by
    intro her
    have ht := h.dist_triangle (u := z) (v := u) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr her] at ht
    omega
  have countMiss {u v : V} (hu : G.Adj z u) (hv : G.Adj z v) (huv : u ≠ v)
      (hnuv : ¬ G.Adj u v) (hAll : ∀ x, x = z ∨ x = u ∨ x = v ∨ x ∈ W ∨ x ∈ R) :
      W.card = s ∧ G.degree u = s ∧
        (∃ p ∈ W, ∀ x ∈ W, G.Adj u x ↔ x ≠ p) ∧
          2 ≤ (R.filter (fun x => 2 < G.dist u x)).card := by
    have hug : s ≤ G.degree u :=
      (Graph189Bipartite.degree_pair u z (G.ne_of_adj hu.symm)).resolve_right (by
        change ¬ s ≤ G.degree z
        rw [hzd]
        exact Nat.not_le.mpr hs)
    have unear (r : V) (hr : r ∈ R) : G.dist u r = 2 ∨ 2 < G.dist u r := by
      have hur : u ≠ r := by
        intro he
        have hm := (mR r).mp hr
        rw [← he,dist_eq_one_iff_adj.mpr hu] at hm
        contradiction
      have hp : 0 < G.dist u r := h.pos_dist_of_ne hur
      have hn : G.dist u r ≠ 1 := fun e => remoteNo hu hr (dist_eq_one_iff_adj.mp e)
      omega
    let D := R.filter (fun x => G.dist u x = 2)
    have vNotR : v ∉ R := by simp [mR,dist_eq_one_iff_adj.mpr hv]
    have hDcap : D.card + 1 ≤ s := by
      have hsub : insert v D ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with e | hh
        · subst x
          simp [two_edges hu.symm hv huv hnuv]
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hh).2⟩
      have hle := (Finset.card_le_card hsub).trans (distance_two_cap s hσ u)
      rwa [Finset.card_insert_of_notMem (fun h => vNotR (Finset.mem_filter.mp h).1)] at hle
    let F := R.filter (fun x => 2 < G.dist u x)
    have hpart : D ∪ F = R := by
      ext x
      simp only [D,F,Finset.mem_union,Finset.mem_filter]
      constructor
      · exact fun he => he.elim And.left And.left
      · intro hx
        exact (unear x hx).imp (fun he => ⟨hx,he⟩) (fun he => ⟨hx,he⟩)
    have hF : 2 ≤ F.card := by
      have hh := Finset.card_union_le D F
      rw [hpart] at hh
      omega
    obtain ⟨r,hr⟩ := Finset.card_pos.mp (by omega : 0 < F.card)
    obtain ⟨p,hpW,hpr⟩ := reachW r (Finset.mem_filter.mp hr).1
    have hMiss : ¬ G.Adj u p := by
      intro hup
      have ht := h.dist_triangle (u := u) (v := p) (w := r)
      have hfar : 2 < G.dist u r := (Finset.mem_filter.mp hr).2
      rw [dist_eq_one_iff_adj.mpr hup,dist_eq_one_iff_adj.mpr hpr] at ht
      omega
    let J := W.filter (G.Adj u)
    have hNJ : G.neighborFinset u = insert z J := by
      ext x
      rw [G.mem_neighborFinset]
      simp only [Finset.mem_insert,Finset.mem_filter,J]
      constructor
      · intro he
        rcases hAll x with rfl | rfl | rfl | hw | hr
        · exact Or.inl rfl
        · exact (G.irrefl he).elim
        · exact (hnuv he).elim
        · exact Or.inr ⟨hw,he⟩
        · exact (remoteNo hu hr he).elim
      · exact fun hh => hh.elim (fun he => he.symm ▸ hu.symm) And.right
    have hzJ : z ∉ J := by simp [J,mW]
    have hJ : J.card + 1 = G.degree u := by
      rw [← Finset.card_insert_of_notMem hzJ,← hNJ,G.card_neighborFinset_eq_degree]
    have hpJ : p ∉ J := fun hm => hMiss (Finset.mem_filter.mp hm).2
    have hIJ : insert p J ⊆ W := by
      intro x hx
      rcases Finset.mem_insert.mp hx with he | hm
      · exact he.symm ▸ hpW
      · exact (Finset.mem_filter.mp hm).1
    have hPM := Finset.card_le_card hIJ
    rw [Finset.card_insert_of_notMem hpJ] at hPM
    have hW' : W.card = s := by omega
    have hu' : G.degree u = s := by omega
    have hIW := Finset.eq_of_subset_of_card_le hIJ (by
      rw [Finset.card_insert_of_notMem hpJ]; omega)
    have hUnique (x : V) (hx : x ∈ W) : G.Adj u x ↔ x ≠ p := by
      constructor
      · exact fun hadj he => hMiss (he ▸ hadj)
      · intro he
        have hx' := hIW.symm ▸ hx
        exact (Finset.mem_filter.mp ((Finset.mem_insert.mp hx').resolve_left he)).2
    exact ⟨hW',hu',⟨p,hpW,hUnique⟩,hF⟩
  have all' (x : V) : x = z ∨ x = b ∨ x = a ∨ x ∈ W ∨ x ∈ R := by
    simpa [or_comm,or_left_comm,or_assoc] using all x
  obtain ⟨hw,ha,⟨p,hp,hap⟩,hra⟩ := countMiss hza hzb hne hab all
  obtain ⟨_,hb,⟨q,hq,hbq⟩,hrb⟩ := countMiss hzb hza hne.symm (fun e => hab e.symm) all'
  have hpq : p ≠ q := by
    intro he
    obtain ⟨u,hzu,hup⟩ := split_two h ((mW p).mp hp)
    have hu : u = a ∨ u = b := by simpa [hZ] using (G.mem_neighborFinset z u).mpr hzu
    rcases hu with ea | eb
    · exact (hap p hp).mp (ea ▸ hup) rfl
    · exact (hbq p hp).mp (eb ▸ hup) he
  exact ⟨hOrder,hw,hRsize,ha,hb,p,hp,q,hq,hpq,hap,hbq,hra,hrb⟩



set_option maxHeartbeats 1000000 in
theorem order_le_three_sigma_of_pair (z : V) (h : G.Connected) (hd : ∀ x, G.dist z x ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b}) :
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
  have anchors {u : V} (hu : G.Adj z u) : u = a ∨ u = b := by
    simpa [hZ] using (G.mem_neighborFinset z u).mpr hu
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hh := hd x
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
    · have hl := large_nonadjacent_layout_rooted z h hd hσ (by exact hs) (by change 2*s+4 ≤ _; omega)
        a b hne hZ hab
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


set_option maxHeartbeats 1000000 in
theorem order_le_three_sigma_sub_one_of_pair (z : V) (h : G.Connected) (hd : ∀ x, G.dist z x ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 4 ≤ G.secondSmallestDegree)
    (a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b}) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree - 1 := by
  classical
  by_contra! hn
  have := h.nonempty
  let s := G.secondSmallestDegree
  have hn' : 3 * s ≤ Fintype.card V := by change 3 * s - 1 < Fintype.card V at hn; omega
  change 4 ≤ s at hs
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  have az : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have bz : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have cap (u : V) : (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s :=
    distance_two_cap s hσ u
  have anchors {u : V} (hu : G.Adj z u) : u = a ∨ u = b := by
    simpa [hZ] using (G.mem_neighborFinset z u).mpr hu
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hh := hd x
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
  have hRlarge : 2 * s - 3 ≤ R.card := by omega
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
    · have hl := large_nonadjacent_layout_rooted z h hd hσ (by omega) (by change 2*s+4 ≤ _; omega)
        a b hne hZ hab
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
  have hRcap : R.card ≤ 2*s-2 := by omega
  have hWlarge : 3 ≤ W.card := by omega
  have hRnot : ¬ 2*s-2 ≤ R.card := by
    intro hSat
    have hDa : Da.card = s - 1 := by omega
    have hDb : Db.card = s - 1 := by omega
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
      rw [Finset.card_erase_of_mem hq',Finset.card_erase_of_mem hpW]
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
    have hz2 : G.dist c z = 2 := by rw [SimpleGraph.dist_comm]; exact (mW c).mp hcW
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
    have hS : S.card ≤ s - 3 := by
      have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩
      dsimp [S]
      rw [Finset.card_erase_of_mem hc,Finset.card_erase_of_mem hq',
        Finset.card_erase_of_mem hpW]
      omega
    have hlow := (Finset.card_le_card hbound).trans (Finset.card_union_le _ _)
    rw [Finset.card_pair hne] at hlow
    have hcNe : c ≠ z := by intro he; have hh := (mW c).mp hcW; simp [he] at hh
    have hhigh : s ≤ G.degree c := (Graph189Bipartite.degree_pair (G := G) c z hcNe).resolve_right (by
      change ¬ s ≤ G.degree z; omega)
    change G.degree c ≤ 2 + S.card at hlow
    omega

  have hR : R.card = 2*s-3 := by omega
  have hW : W.card = s := by omega
  let D (u : V) := R.filter (fun r => G.dist u r = 2)
  let M (u : V) := W.filter (fun w => ¬ G.Adj u w)
  have good {v : V} (hv : v ≠ z) : s ≤ G.degree v :=
    (Graph189Bipartite.degree_pair (G := G) v z hv).resolve_right (by
      change ¬ s ≤ G.degree z
      omega)
  have notZ {v : V} (hv : v ∈ W ∨ v ∈ R) : v ≠ z := by
    intro e
    subst v
    rcases hv with he | he
    · simp [mW] at he
    · simp [mR] at he
  have noLayer {v u : V} (hv : v ∈ W ∨ v ∈ R) (hu : G.Adj z u) : v ≠ u := by
    intro e
    subst v
    rcases hv with he | he
    · simp [mW,dist_eq_one_iff_adj.mpr hu] at he
    · simp [mR,dist_eq_one_iff_adj.mpr hu] at he
  have wNotR {v : V} (hv : v ∈ W) : v ∉ R := by
    intro he
    have hw := (mW v).mp hv
    have hr := (mR v).mp he
    omega
  have side (u : V) {r : V} (hu : G.Adj z u) (hr : r ∈ R)
      (hn : r ∉ D u) {w : V} (hw : w ∈ W) (hwr : G.Adj w r) : w ∈ M u :=
    Finset.mem_filter.mpr ⟨hw,fun huw =>
      hn (Finset.mem_filter.mpr ⟨hr,remoteTwo hu hr huw hwr⟩)⟩
  have miss_form (u : V) (A : Finset V) (he : M u = A) (x : V) (hx : x ∈ W) :
      G.Adj u x ↔ x ∉ A := by
    rw [← he]
    simp [M,hx]
  have remoteNbr (r : V) (hr : r ∈ R) (x : V) (hxr : G.Adj x r) : x ∈ W ∨ x ∈ R := by
    rcases all x with e | e | e | hw | hR
    · subst x
      have hh := (mR r).mp hr
      rw [dist_eq_one_iff_adj.mpr hxr] at hh
      contradiction
    · exact (remoteNo az hr (e ▸ hxr)).elim
    · exact (remoteNo bz hr (e ▸ hxr)).elim
    · exact Or.inl hw
    · exact Or.inr hR
  have onlyMiss (u : V) (hu : G.Adj z u) (p : V) (hp : M u = {p})
      (r : V) (hr : r ∈ R) (hn : r ∉ D u) :
      G.Adj p r ∧ ∀ w ∈ W, G.Adj w r → w = p := by
    have wOnly (w : V) (hw : w ∈ W) (hwr : G.Adj w r) : w = p :=
      by simpa [hp] using side u hu hr hn hw hwr
    obtain ⟨w,hw,hwr⟩ := reachW hr
    exact ⟨wOnly w hw hwr ▸ hwr,wOnly⟩
  have anchorCoverage (u v : V) (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) :
      ∀ w ∈ W, G.Adj u w ∨ G.Adj v w := by
    intro w hw
    rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact reachAnchor hw
    · exact (reachAnchor hw).symm
  have unionCoverage (u v : V) (huv : (u = a ∧ v = b) ∨ (u = b ∧ v = a)) : D u ∪ D v = R := by
    rcases huv with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact coverR
    · rw [Finset.union_comm]
      exact coverR
  have twoMiss (u v : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (orientation : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
      (hum : (M u).card = 1) (hvm : (M v).card = 1)
      (hDu : (D u).card = s-1)
      (hcase : ((D v).card = s-2 ∧ Disjoint (D u) (D v)) ∨
        ((D v).card = s-1 ∧ ((D u) ∩ (D v)).card = 1)) : False := by
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hum
    obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hvm
    have hpW : p ∈ W := (Finset.mem_filter.mp (show p ∈ M u by simp [hp])).1
    have hqW : q ∈ W := (Finset.mem_filter.mp (show q ∈ M v by simp [hq])).1
    have coverage := anchorCoverage u v orientation
    have hpu : ¬ G.Adj u p := fun he => (miss_form u {p} hp p hpW).mp he (by simp)
    have hqv : ¬ G.Adj v q := fun he => (miss_form v {q} hq q hqW).mp he (by simp)
    have hpq : p ≠ q := fun e => (coverage p hpW).elim hpu (fun he => hqv (e ▸ he))
    have hpv : G.Adj p v := ((coverage p hpW).resolve_left hpu).symm
    have hqu : G.Adj q u := ((coverage q hqW).resolve_right hqv).symm
    let S := (W.erase p).erase q
    let P := D v \ D u
    let Q := D u \ D v
    let T := D u ∩ D v
    have hU := unionCoverage u v orientation
    have sW : S ⊆ W := fun _ he => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
    have pR : P ⊆ R := fun _ he => (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).1
    have qR : Q ⊆ R := fun _ he => (Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1).1
    have hS : S.card = s-2 := by
      dsimp [S]
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hpq.symm,hqW⟩),
        Finset.card_erase_of_mem hpW,hW]
      omega
    have hSP : Disjoint S P := Finset.disjoint_left.mpr (fun x hs hp => wNotR (sW hs) (pR hp))
    have hSQ : Disjoint S Q := Finset.disjoint_left.mpr (fun x hs hq => wNotR (sW hs) (qR hq))
    have hPQ : Disjoint P Q := Finset.disjoint_left.mpr (fun x hx hy =>
      (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1)
    have hAnch (c : V) (hc : c ∈ S) : G.Adj u c ∧ G.Adj v c ∧ G.dist c z = 2 := by
      have hcW := sW hc
      refine ⟨(miss_form u {p} hp c hcW).mpr (by simpa using Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)),
        (miss_form v {q} hq c hcW).mpr (by simpa using Finset.ne_of_mem_erase hc),?_⟩
      rw [SimpleGraph.dist_comm]
      exact (mW c).mp hcW
    have pp (r : V) (hr : r ∈ P) : G.Adj p r ∧ ∀ w ∈ W, G.Adj w r → w = p :=
      onlyMiss u hu p hp r (pR hr) (Finset.mem_sdiff.mp hr).2
    have qq (r : V) (hr : r ∈ Q) : G.Adj q r ∧ ∀ w ∈ W, G.Adj w r → w = q :=
      onlyMiss v hv q hq r (qR hr) (Finset.mem_sdiff.mp hr).2
    have hnS (c : V) (hc : c ∈ S) (r : V) (hr : r ∈ P ∪ Q) : ¬ G.Adj c r := by
      intro he
      rcases Finset.mem_union.mp hr with heP | heQ
      · exact (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)) ((pp r heP).2 c (sW hc) he)
      · exact (Finset.ne_of_mem_erase hc) ((qq r heQ).2 c (sW hc) he)
    have hsplit : P ∪ Q ∪ T = R := by
      rw [← hU]
      ext x
      simp only [P,Q,T,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
      tauto
    have nP (r : V) (hr : r ∈ P) : G.neighborFinset r ⊆ insert p (P ∪ Q ∪ T) := by
      intro x hx
      have he := ((G.mem_neighborFinset r x).mp hx).symm
      rcases remoteNbr r (pR hr) x he with hw | hR
      · exact Finset.mem_insert.mpr (Or.inl ((pp r hr).2 x hw he))
      · exact Finset.mem_insert_of_mem (hsplit.symm ▸ hR)
    have nQ (r : V) (hr : r ∈ Q) : G.neighborFinset r ⊆ insert q (Q ∪ P ∪ T) := by
      intro x hx
      have he := ((G.mem_neighborFinset r x).mp hx).symm
      rcases remoteNbr r (qR hr) x he with hw | hR
      · exact Finset.mem_insert.mpr (Or.inl ((qq r hr).2 x hw he))
      · rw [Finset.union_comm Q P, hsplit]
        exact Finset.mem_insert_of_mem hR
    have hzS : z ∉ S := fun he => notZ (Or.inl (sW he)) rfl
    have hzP : z ∉ P := fun he => notZ (Or.inr (pR he)) rfl
    have hzQ : z ∉ Q := fun he => notZ (Or.inr (qR he)) rfl
    have hpS : p ∉ S := fun he => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he) rfl
    have hqS : q ∉ S := fun he => Finset.ne_of_mem_erase he rfl
    have pdz : G.dist p z = 2 := by rw [SimpleGraph.dist_comm]; exact (mW p).mp hpW
    have qdz : G.dist q z = 2 := by rw [SimpleGraph.dist_comm]; exact (mW q).mp hqW
    have hPm (r : V) (hr : r ∈ P) : G.Adj p r ∧ ¬ G.Adj q r :=
      ⟨(pp r hr).1,fun he => hpq ((pp r hr).2 q hqW he).symm⟩
    have hQm (r : V) (hr : r ∈ Q) : G.Adj q r ∧ ¬ G.Adj p r :=
      ⟨(qq r hr).1,fun he => hpq ((qq r hr).2 p hpW he)⟩
    have CP : P.card = (D v).card - T.card := by
      dsimp [P,T]
      rw [Finset.card_sdiff,Finset.inter_comm]
    have CQ : Q.card = (D u).card - T.card := by
      dsimp [Q,T]
      rw [Finset.card_sdiff,Finset.inter_comm]
    rcases hcase with ⟨hDv,hd⟩ | ⟨hDv,ht⟩
    · have ht : T = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
      have hP : P.card = s-2 := by simp [CP,hDv,ht]
      have hQ : Q.card = s-1 := by simp [CQ,hDu,ht]
      exact disjoint_two_misses_impossible s hs cap S P Q hS hP hQ hSP hSQ hPQ z u v p q
        hzS hzP hzQ hpS hqS (fun he => wNotR hpW (qR he))
        (fun he => wNotR hqW (pR he)) (notZ (Or.inl hpW)).symm hpv hqu qdz hAnch hnS
        (fun r hr => good (notZ (Or.inr (pR hr))))
        (fun r hr => by simpa [ht] using nP r hr) hPm (fun r hr => (hQm r hr).1)
    · have hP : P.card = s-2 := by rw [CP,hDv]; change T.card = 1 at ht; omega
      have hQ : Q.card = s-2 := by rw [CQ,hDu]; change T.card = 1 at ht; omega
      exact overlap_impossible s hs cap S P Q T hS hP hQ (by exact ht.le)
        hSP hSQ hPQ z u v p q hzS hzP hzQ
        (fun he => noLayer (Or.inl (sW he)) hu rfl)
        (fun he => noLayer (Or.inr (qR he)) hu rfl) (G.ne_of_adj hu.symm)
        (fun he => noLayer (Or.inl (sW he)) hv rfl)
        (fun he => noLayer (Or.inr (pR he)) hv rfl) (G.ne_of_adj hv.symm)
        (fun he => hpu he.symm) (noLayer (Or.inl hpW) hu) hpv
        (fun he => hqv he.symm) (noLayer (Or.inl hqW) hv) hqu
        hpS hqS (fun he => wNotR hqW (pR he)) (fun he => wNotR hpW (qR he)) pdz qdz hAnch hnS
        (fun r hr => good (notZ (Or.inr (pR hr)))) (fun r hr => good (notZ (Or.inr (qR hr))))
        nP nQ hPm hQm
  have threeMiss (u v : V) (hu : G.Adj z u) (hv : G.Adj z v)
      (orientation : (u = a ∧ v = b) ∨ (u = b ∧ v = a))
      (hum : (M u).card = 1) (hvm : (M v).card = 2)
      (hDu : (D u).card = s-1) (hDv : (D v).card = s-2)
      (dd : Disjoint (D u) (D v)) : False := by
    obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hum
    obtain ⟨q₁,q₂,hqq,hq⟩ := Finset.card_eq_two.mp hvm
    let P := D v
    let Q := D u
    have hpW : p ∈ W := (Finset.mem_filter.mp (show p ∈ M u by simp [hp])).1
    have h₁W : q₁ ∈ W := (Finset.mem_filter.mp (show q₁ ∈ M v by simp [hq])).1
    have h₂W : q₂ ∈ W := (Finset.mem_filter.mp (show q₂ ∈ M v by simp [hq])).1
    have cv := anchorCoverage u v orientation
    have hpu : ¬ G.Adj u p := fun he => (miss_form u {p} hp p hpW).mp he (by simp)
    have h₁v : ¬ G.Adj v q₁ := fun he => (miss_form v {q₁,q₂} hq q₁ h₁W).mp he (by simp)
    have h₂v : ¬ G.Adj v q₂ := fun he => (miss_form v {q₁,q₂} hq q₂ h₂W).mp he (by simp)
    have hp₁ : p ≠ q₁ := fun e => (cv p hpW).elim hpu (fun he => h₁v (e ▸ he))
    have hp₂ : p ≠ q₂ := fun e => (cv p hpW).elim hpu (fun he => h₂v (e ▸ he))
    have hpv : G.Adj p v := ((cv p hpW).resolve_left hpu).symm
    have h₁u : G.Adj q₁ u := ((cv q₁ h₁W).resolve_right h₁v).symm
    have h₂u : G.Adj q₂ u := ((cv q₂ h₂W).resolve_right h₂v).symm
    have hU := unionCoverage u v orientation
    have pR : P ⊆ R := Finset.filter_subset _ _
    have qR : Q ⊆ R := Finset.filter_subset _ _
    have hPQ : Disjoint P Q := dd.symm
    have hR' : P ∪ Q = R := by rw [Finset.union_comm]; exact hU
    have hAble : 0 < (((W.erase p).erase q₁).erase q₂).card := by
      have h₁' : q₁ ∈ W.erase p := Finset.mem_erase.mpr ⟨hp₁.symm,h₁W⟩
      have h₂' : q₂ ∈ (W.erase p).erase q₁ :=
        Finset.mem_erase.mpr ⟨hqq.symm,Finset.mem_erase.mpr ⟨hp₂.symm,h₂W⟩⟩
      rw [Finset.card_erase_of_mem h₂',Finset.card_erase_of_mem h₁',Finset.card_erase_of_mem hpW,hW]
      omega
    obtain ⟨c,hc⟩ := Finset.card_pos.mp hAble
    have hc₂ := Finset.ne_of_mem_erase hc
    have hc₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    have hcp := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
    have hcW : c ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc))
    have hcu : G.Adj c u := ((miss_form u {p} hp c hcW).mpr (by simpa using hcp)).symm
    have hcv : G.Adj c v := ((miss_form v {q₁,q₂} hq c hcW).mpr (by simp [hc₁,hc₂])).symm
    have pp (r : V) (hr : r ∈ P) : G.Adj p r ∧ ∀ w ∈ W, G.Adj w r → w = p :=
      onlyMiss u hu p hp r (pR hr) (fun he => Finset.disjoint_left.mp dd he hr)
    have qSide (r : V) (hr : r ∈ Q) (w : V) (hw : w ∈ W) (he : G.Adj w r) :
        w = q₁ ∨ w = q₂ := by
      simpa [hq] using side v hv (qR hr) (fun he => Finset.disjoint_left.mp dd hr he) hw he
    have qTouch (r : V) (hr : r ∈ Q) : G.Adj q₁ r ∨ G.Adj q₂ r := by
      obtain ⟨w,hw,hwr⟩ := reachW (qR hr)
      rcases qSide r hr w hw hwr with e | e
      · exact Or.inl (e ▸ hwr)
      · exact Or.inr (e ▸ hwr)
    have noRemoteC (r : V) (hr : r ∈ P ∪ Q) : ¬ G.Adj c r := by
      intro he
      rcases Finset.mem_union.mp hr with rr | rr
      · exact hcp ((pp r rr).2 c hcW he)
      · exact (qSide r rr c hcW he).elim hc₁ hc₂
    have middle_neighbors (x : V) (hx : x ∈ W) (hxr : ∀ r ∈ R, ¬ G.Adj x r) (w : V)
        (he : G.Adj x w) : w = u ∨ w = v ∨ w ∈ W.erase x := by
      have cover (y : V) : y = z ∨ y = u ∨ y = v ∨ y ∈ W ∨ y ∈ R := by
        rcases orientation with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact all y
        · simpa [or_comm,or_left_comm,or_assoc] using all y
      rcases cover w with eq | eq | eq | hw | hw
      · subst w
        have hdx := (mW x).mp hx
        rw [dist_eq_one_iff_adj.mpr he.symm] at hdx
        contradiction
      · exact Or.inl eq
      · exact Or.inr (Or.inl eq)
      · exact Or.inr (Or.inr (Finset.mem_erase.mpr ⟨(G.ne_of_adj he).symm,hw⟩))
      · exact (hxr w hw he).elim
    have cpair {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hcx : x ≠ c) (hcy : y ≠ c) :
        G.Adj c x ∨ G.Adj c y := by
      by_contra! hn
      have hsub : G.neighborFinset c ⊆ insert u (insert v ((((W.erase c).erase x).erase y))) := by
        intro w hw
        have he := (G.mem_neighborFinset c w).mp hw
        rcases middle_neighbors c hcW (fun r hr => noRemoteC r (hR'.symm ▸ hr)) w he with eq | eq | hw'
        · exact Finset.mem_insert.mpr (Or.inl eq)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq))
        · have hwx : w ≠ x := fun eq => hn.1 (eq ▸ he)
          have hwy : w ≠ y := fun eq => hn.2 (eq ▸ he)
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hwy,Finset.mem_erase.mpr ⟨hwx,hw'⟩⟩))
      have hcard := Finset.card_le_card hsub
      have h1 := Finset.card_insert_le u (insert v (((W.erase c).erase x).erase y))
      have h2 := Finset.card_insert_le v (((W.erase c).erase x).erase y)
      have hx' : x ∈ W.erase c := Finset.mem_erase.mpr ⟨hcx,hx⟩
      have hy' : y ∈ (W.erase c).erase x :=
        Finset.mem_erase.mpr ⟨hxy.symm,Finset.mem_erase.mpr ⟨hcy,hy⟩⟩
      rw [Finset.card_erase_of_mem hy',Finset.card_erase_of_mem hx',
        Finset.card_erase_of_mem hcW,hW] at h2
      have hgc := good (notZ (Or.inl hcW))
      change s ≤ (G.neighborFinset c).card at hgc
      omega
    have noPside (w : V) (hw : w ∈ W) (hwp : w ≠ p) (r : V) (hr : r ∈ P) : ¬ G.Adj w r :=
      fun he => hwp ((pp r hr).2 w hw he)
    have full (w : V) (hw : w ∈ W) (hwp : w ≠ p) (hwv : ¬ G.Adj w v)
        (hnoQ : ∀ r ∈ Q, ¬ G.Adj w r) :
        ∀ x ∈ W, x ≠ w → G.Adj w x := by
      have hsub : G.neighborFinset w ⊆ insert u (W.erase w) := by
        intro x hx
        have he := (G.mem_neighborFinset w x).mp hx
        have hnr (r : V) (hr : r ∈ R) : ¬ G.Adj w r := by
          rw [← hR'] at hr
          exact (Finset.mem_union.mp hr).elim (noPside w hw hwp r) (hnoQ r)
        rcases middle_neighbors w hw hnr x he with eq | eq | hx'
        · exact Finset.mem_insert.mpr (Or.inl eq)
        · exact (hwv (eq ▸ he)).elim
        · exact Finset.mem_insert_of_mem hx'
      have hcap := Finset.card_insert_le u (W.erase w)
      rw [Finset.card_erase_of_mem hw,hW] at hcap
      have hg := good (notZ (Or.inl hw))
      change s ≤ (G.neighborFinset w).card at hg
      have hEq := Finset.eq_of_subset_of_card_le hsub (by omega)
      intro x hx hne
      apply (G.mem_neighborFinset w x).mp
      rw [hEq]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hne,hx⟩)
    have zdist (x : V) (hx : x ∈ W) : G.dist x z = 2 := by rw [SimpleGraph.dist_comm]; exact (mW x).mp hx
    exact disjoint_three_misses_impossible s hs cap P Q hDv hDu hPQ z c u v p q₁ q₂
      (fun he => notZ (Or.inr (pR he)) rfl) (fun he => notZ (Or.inr (qR he)) rfl)
      (fun he => wNotR hpW (qR he)) (fun he => wNotR h₁W (pR he)) (fun he => wNotR h₂W (pR he))
      (fun he => wNotR h₁W (qR he)) (fun he => wNotR h₂W (qR he)) (fun he => wNotR hcW (pR he)) (fun he => wNotR hcW (qR he))
      (notZ (Or.inl hpW)) (notZ (Or.inl h₁W)) (notZ (Or.inl h₂W))
      hcp hc₁ hc₂ (zdist c hcW) (zdist q₁ h₁W) (zdist q₂ h₂W) hcu hcv hpv h₁u h₂u
      noRemoteC (fun r hr => (pp r hr).1) qTouch
      (noPside q₁ h₁W hp₁.symm) (noPside q₂ h₂W hp₂.symm)
      (cpair hpW h₁W hp₁ hcp.symm hc₁.symm) (cpair hpW h₂W hp₂ hcp.symm hc₂.symm)
      (cpair h₁W h₂W hqq hc₁.symm hc₂.symm)
      (fun he => ⟨full q₁ h₁W hp₁.symm (fun e => h₁v e.symm) he p hpW hp₁,
        full q₁ h₁W hp₁.symm (fun e => h₁v e.symm) he q₂ h₂W hqq.symm⟩)
      (fun he => ⟨full q₂ h₂W hp₂.symm (fun e => h₂v e.symm) he p hpW hp₂,
        full q₂ h₂W hp₂.symm (fun e => h₂v e.symm) he q₁ h₁W hqq⟩)
  have hCoverCount : (Da ∪ Db).card = 2*s-3 := by rw [coverR,hR]
  rcases near_partition_counts s Ma.card Mb.card hs Da Db hCoverCount ha hb la lb with
    ⟨hma,hmb,hda,hdb,hi⟩ | ⟨hma,hmb,hdSizes,dd⟩ | ⟨hdSizes,dd⟩
  · exact twoMiss a b az bz (Or.inl ⟨rfl,rfl⟩) hma hmb hda (Or.inr ⟨hdb,hi⟩)
  · rcases hdSizes with ⟨hda,hdb⟩ | ⟨hdb,hda⟩
    · exact twoMiss a b az bz (Or.inl ⟨rfl,rfl⟩) hma hmb hda (Or.inl ⟨hdb,dd⟩)
    · exact twoMiss b a bz az (Or.inr ⟨rfl,rfl⟩) hmb hma hdb (Or.inl ⟨hda,dd.symm⟩)
  · rcases hdSizes with ⟨hma,hmb,hda,hdb⟩ | ⟨hma,hmb,hda,hdb⟩
    · exact threeMiss a b az bz (Or.inl ⟨rfl,rfl⟩) hma hmb hda hdb dd
    · exact threeMiss b a bz az (Or.inr ⟨rfl,rfl⟩) hmb hma hdb hda dd.symm


theorem order_le_three_sigma_sub_one (z : V) (h : G.Connected) (hd : ∀ x, G.dist z x ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 4 ≤ G.secondSmallestDegree) (hz : G.degree z = 2) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree - 1 := by
  obtain ⟨a,b,hne,hpair⟩ := Finset.card_eq_two.mp (show (G.neighborFinset z).card = 2 from hz)
  exact order_le_three_sigma_sub_one_of_pair z h hd hσ hs a b hne hpair

theorem order_le_three_sigma (z : V) (h : G.Connected) (hd : ∀ x, G.dist z x ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree) (hz : G.degree z = 2) :
    Fintype.card V ≤ 3 * G.secondSmallestDegree := by
  obtain ⟨a,b,hne,hpair⟩ := Finset.card_eq_two.mp (show (G.neighborFinset z).card = 2 from hz)
  exact order_le_three_sigma_of_pair z h hd hσ hs a b hne hpair

#print axioms order_le_three_sigma_sub_one
#print axioms order_le_three_sigma
end Graph189DegreeTwoRooted
