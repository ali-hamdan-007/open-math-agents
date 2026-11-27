import Graph189DegreeTwoFinalBound

namespace Graph189Order14Layout
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

set_option maxHeartbeats 500000 in
/-- At order fourteen and second-smallest degree five, there are five
possible anchor patterns up to exchanging the two neighbors. -/
theorem shapes (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 5) (hn : Fintype.card V = 14)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b}) :
    let W := Finset.univ.filter (fun v => G.dist z v = 2)
    let ma := (W.filter (fun w => ¬G.Adj a w)).card
    let mb := (W.filter (fun w => ¬G.Adj b w)).card
    (W.card = 4 ∧ G.Adj a b ∧ ma = 1 ∧ mb = 1) ∨
      (W.card = 5 ∧ ¬ G.Adj a b ∧ ma = 1 ∧ mb = 1) ∨
      (W.card = 5 ∧ G.Adj a b ∧ 1 ≤ ma ∧ ma ≤ 2 ∧ 1 ≤ mb ∧ mb ≤ 2) := by
  classical
  have := h.nonempty
  let s := G.secondSmallestDegree
  change s = 5 at hs
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
  have hRlarge : s + 1 ≤ R.card := by omega
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
    · have hl := large_nonadjacent_layout h hd hσ (by omega) (by change 2*s+4 ≤ _; omega)
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
  change (W.card = 4 ∧ G.Adj a b ∧ Ma.card = 1 ∧ Mb.card = 1) ∨
      (W.card = 5 ∧ ¬ G.Adj a b ∧ Ma.card = 1 ∧ Mb.card = 1) ∨
      (W.card = 5 ∧ G.Adj a b ∧ 1 ≤ Ma.card ∧ Ma.card ≤ 2 ∧ 1 ≤ Mb.card ∧ Mb.card ≤ 2)
  have degreeCap (u v : V) (hu : G.Adj z u)
      (hall : ∀ x : V, x = z ∨ x = u ∨ x = v ∨ x ∈ W ∨ x ∈ R) :
      s ≤ 2 + (W.card - (W.filter (fun w => ¬ G.Adj u w)).card) := by
    let M := W.filter (fun w => ¬ G.Adj u w)
    have hg : s ≤ G.degree u :=
      (Graph189Bipartite.degree_pair (G := G) u z (G.ne_of_adj hu.symm)).resolve_right (by
        change ¬ s ≤ G.degree z
        omega)
    have hsub : G.neighborFinset u ⊆ insert z (insert v (W \ M)) := by
      intro x he
      have hux := (G.mem_neighborFinset u x).mp he
      rcases hall x with eq | eq | eq | hw | hr
      · exact Finset.mem_insert.mpr (Or.inl eq)
      · exact (G.ne_of_adj hux eq.symm).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq))
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_sdiff.mpr ⟨hw,fun hm => (Finset.mem_filter.mp hm).2 hux⟩))
      · exact (remoteNo hu hr hux).elim
    have h₁ := Finset.card_le_card hsub
    have h₂ := Finset.card_insert_le z (insert v (W \ M))
    have h₃ := Finset.card_insert_le v (W \ M)
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _)] at h₃
    change (insert v (W \ M)).card ≤ W.card - M.card + 1 at h₃
    change s ≤ (G.neighborFinset u).card at hg
    change s ≤ 2 + (W.card - M.card)
    omega
  have all' (x : V) : x = z ∨ x = b ∨ x = a ∨ x ∈ W ∨ x ∈ R := by
    simpa [or_comm,or_left_comm,or_assoc] using all x
  have hA := degreeCap a b az all
  have hB := degreeCap b a bz all'
  change s ≤ 2 + (W.card - Ma.card) at hA
  change s ≤ 2 + (W.card - Mb.card) at hB
  by_cases hab : G.Adj a b
  · by_cases hW : W.card = 4
    · exact Or.inl ⟨hW,hab,by omega,by omega⟩
    · exact Or.inr (Or.inr ⟨by omega,hab,ha,by omega,hb,by omega⟩)
  · have hl := large_nonadjacent_layout h hd hσ (by omega) (by omega) z a b hne hZ hab
    obtain ⟨_,hW,_,_,_,p,hp,q,hq,_,hap,hbq,_,_⟩ := hl
    change W.card = s at hW
    have missCard (u p : V) (hp : p ∈ W)
        (hmiss : ∀ x ∈ W, G.Adj u x ↔ x ≠ p) :
        (W.filter (fun w => ¬G.Adj u w)).card = 1 := by
      have he : W.filter (fun w => ¬G.Adj u w) = {p} := by
        ext x
        constructor
        · intro hm
          obtain ⟨hW,hn⟩ := Finset.mem_filter.mp hm
          exact Finset.mem_singleton.mpr (by by_contra! h; exact hn ((hmiss x hW).mpr h))
        · intro hm
          have hh := Finset.mem_singleton.mp hm
          subst x
          exact Finset.mem_filter.mpr ⟨hp,fun he => (hmiss p hp).mp he rfl⟩
      simp [he]
    exact Or.inr (Or.inl ⟨by omega,hab,missCard a p hp hap,missCard b q hq hbq⟩)

#print axioms shapes
end Graph189Order14Layout
