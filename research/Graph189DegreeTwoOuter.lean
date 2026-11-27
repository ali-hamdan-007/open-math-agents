import Graph189DistanceLayers
import Graph189BipartiteStructure

namespace Graph189DegreeTwoOuter
open SimpleGraph Graph189LowDegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem distance_two_cap (s : ℕ) (hσ : ∀ x, G.distEven x ≤ 1 + s) (x : V) :
    (Finset.univ.filter (fun v => G.dist x v = 2)).card ≤ s := by
  let D := Finset.univ.filter (fun v => G.dist x v = 2)
  have hsub : insert x D ⊆ Finset.univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hv with rfl | hmem
    · simp
    · exact (Finset.mem_filter.mp hmem).2 ▸ (by decide : Even 2)
  have hne : x ∉ D := by simp [D]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hne] at hle
  change D.card + 1 ≤ G.distEven x at hle
  change D.card ≤ s
  have h := hσ x
  omega

/-- Outside the small-order range, neither neighbor of a degree-two vertex can
see the entire distance-two layer. With nonadjacent neighbors, each must miss
exactly one member of that layer. -/
theorem large_nonadjacent_layout (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : 3 ≤ G.secondSmallestDegree)
    (hn : 2 * G.secondSmallestDegree + 4 ≤ Fintype.card V)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b})
    (hab : ¬ G.Adj a b) :
    let W := Finset.univ.filter (fun v => G.dist z v = 2)
    let R := Finset.univ.filter (fun v => G.dist z v = 3)
    W.card + R.card + 3 = Fintype.card V ∧
    W.card = G.secondSmallestDegree ∧ G.secondSmallestDegree + 1 ≤ R.card ∧
      G.degree a = G.secondSmallestDegree ∧ G.degree b = G.secondSmallestDegree ∧
        ∃ p ∈ W, ∃ q ∈ W, p ≠ q ∧
          (∀ x ∈ W, G.Adj a x ↔ x ≠ p) ∧ (∀ x ∈ W, G.Adj b x ↔ x ≠ q) ∧
          2 ≤ (R.filter (fun x => G.dist a x = 3)).card ∧
          2 ≤ (R.filter (fun x => G.dist b x = 3)).card := by
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
  have ds (x y : V) : G.dist x y ≤ 3 :=
    (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := y)).trans hd
  have all (x : V) : x = z ∨ x = a ∨ x = b ∨ x ∈ W ∨ x ∈ R := by
    have hc : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by
      have := ds z x
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
          2 ≤ (R.filter (fun x => G.dist u x = 3)).card := by
    have hug : s ≤ G.degree u :=
      (Graph189Bipartite.degree_pair u z (G.ne_of_adj hu.symm)).resolve_right (by
        change ¬ s ≤ G.degree z
        rw [hzd]
        exact Nat.not_le.mpr hs)
    have unear (r : V) (hr : r ∈ R) : G.dist u r = 2 ∨ G.dist u r = 3 := by
      have hur : u ≠ r := by
        intro he
        have hm := (mR r).mp hr
        rw [← he,dist_eq_one_iff_adj.mpr hu] at hm
        contradiction
      have hp : 0 < G.dist u r := h.pos_dist_of_ne hur
      have hn : G.dist u r ≠ 1 := fun e => remoteNo hu hr (dist_eq_one_iff_adj.mp e)
      have hm := ds u r
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
    let F := R.filter (fun x => G.dist u x = 3)
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
      rw [(Finset.mem_filter.mp hr).2,dist_eq_one_iff_adj.mpr hup,dist_eq_one_iff_adj.mpr hpr] at ht
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


omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
/-- In the large-order layout, a remote vertex sees just the missed vertex
in the middle layer. -/
theorem remote_unique_middle (h : G.Connected) {z u p r : V}
    (hr : G.dist z r = 3) (hur : G.dist u r = 3)
    (hmiss : ∀ x : V, G.dist z x = 2 → (G.Adj u x ↔ x ≠ p)) :
    G.Adj p r ∧ ∀ x : V, G.dist z x = 2 → G.Adj x r → x = p := by
  have only (x : V) (hx : G.dist z x = 2) (hxr : G.Adj x r) : x = p := by
    by_contra hne
    have hux := (hmiss x hx).mpr hne
    have ht := h.dist_triangle (u := u) (v := x) (w := r)
    rw [hur,dist_eq_one_iff_adj.mpr hux,dist_eq_one_iff_adj.mpr hxr] at ht
    omega
  obtain ⟨x,hx,hxr⟩ := split_three h hr
  exact ⟨only x hx hxr ▸ hxr,only⟩

/-- At order ten with second-smallest degree three, a degree-two vertex cannot
have nonadjacent neighbors. -/
theorem not_order_ten_of_nonadjacent (h : G.Connected) (hd : G.diam ≤ 3)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (hs : G.secondSmallestDegree = 3)
    (z a b : V) (hne : a ≠ b) (hZ : G.neighborFinset z = {a,b})
    (hab : ¬ G.Adj a b) :
    Fintype.card V ≠ 10 := by
  classical
  intro hn
  let W := Finset.univ.filter (fun v => G.dist z v = 2)
  let R := Finset.univ.filter (fun v => G.dist z v = 3)
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hne]
  have hL := large_nonadjacent_layout h hd hσ (by omega) (by omega)
    z a b hne hZ hab
  change W.card + R.card + 3 = Fintype.card V ∧ W.card = G.secondSmallestDegree ∧ _ at hL
  obtain ⟨hOrder,hW,_,_,_,p,hp,q,hq,hpq,hap,hbq,hRa,hRb⟩ := hL
  have hWcard : W.card = 3 := hW.trans hs
  have hRcard : R.card = 4 := by omega
  have mW (x : V) : x ∈ W ↔ G.dist z x = 2 := by simp [W]
  have mR (x : V) : x ∈ R ↔ G.dist z x = 3 := by simp [R]
  let X := R.filter (fun x => G.dist a x = 3)
  let Y := R.filter (fun x => G.dist b x = 3)
  change 2 ≤ X.card at hRa
  change 2 ≤ Y.card at hRb
  have hxOnly {r : V} (hr : r ∈ X) :
      G.Adj p r ∧ ∀ x ∈ W, G.Adj x r → x = p := by
    obtain ⟨hr',ha⟩ := Finset.mem_filter.mp hr
    obtain ⟨hp',hu⟩ := remote_unique_middle h ((mR r).mp hr') ha
      (fun x hx => hap x ((mW x).mpr hx))
    exact ⟨hp',fun x hx => hu x ((mW x).mp hx)⟩
  have hyOnly {r : V} (hr : r ∈ Y) :
      G.Adj q r ∧ ∀ x ∈ W, G.Adj x r → x = q := by
    obtain ⟨hr',ha⟩ := Finset.mem_filter.mp hr
    obtain ⟨hq',hu⟩ := remote_unique_middle h ((mR r).mp hr') ha
      (fun x hx => hbq x ((mW x).mpr hx))
    exact ⟨hq',fun x hx => hu x ((mW x).mp hx)⟩
  have hdis : Disjoint X Y := by
    refine Finset.disjoint_left.mpr ?_
    intro r hrX hrY
    exact hpq ((hyOnly hrY).2 p hp (hxOnly hrX).1)
  have hcoverR : X ∪ Y = R := by
    apply Finset.eq_of_subset_of_card_le (Finset.union_subset (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))
    rw [Finset.card_union_of_disjoint hdis,hRcard]
    omega
  have hWdiff : 0 < ((W.erase p).erase q).card := by
    have hq' : q ∈ W.erase p := Finset.mem_erase.mpr ⟨hpq.symm,hq⟩
    rw [Finset.card_erase_of_mem hq',Finset.card_erase_of_mem hp,hWcard]
    decide
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hWdiff
  have hcq : c ≠ q := Finset.ne_of_mem_erase hc
  have hcp : c ≠ p := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcW : c ∈ W := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hWcover : ({p,q,c} : Finset V) = W := by
    apply Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rcases (show x = p ∨ x = q ∨ x = c from by simpa using hx) with e | e | e
      · exact e.symm ▸ hp
      · exact e.symm ▸ hq
      · exact e.symm ▸ hcW
    · rw [hWcard]
      simp [Finset.card_insert_of_notMem,hpq,hcp.symm,hcq.symm]
  have remote_adj (v r : V) (hv : G.Adj z v) (hr : r ∈ R) : ¬ G.Adj v r := by
    intro hvr
    have ht := h.dist_triangle (u := z) (v := v) (w := r)
    rw [(mR r).mp hr,dist_eq_one_iff_adj.mpr hv,dist_eq_one_iff_adj.mpr hvr] at ht
    omega
  have reserve {u v p q : V} {D : Finset V} (hu : G.Adj z u) (hv : G.Adj z v)
      (huv : u ≠ v) (hnuv : ¬ G.Adj u v)
      (hpW : p ∈ W) (hup : ¬ G.Adj u p) (huc : G.Adj u c)
      (huq : G.Adj u q) (hD : 2 ≤ D.card) (hDR : D ⊆ R)
      (hDq : ∀ r ∈ D, G.Adj q r) :
      ¬ G.Adj c p := by
    intro hcAdj
    have hnep : u ≠ p := by
      intro he
      have h := (mW p).mp hpW
      rw [← he,dist_eq_one_iff_adj.mpr hu] at h
      contradiction
    have ph : G.dist u p = 2 := two_edges huc hcAdj hnep hup
    have vh : G.dist u v = 2 := two_edges hu.symm hv huv hnuv
    have hnear (r : V) (hr : r ∈ D) : G.dist u r = 2 := by
      have hr' := hDR hr
      have hne : u ≠ r := by
        intro he
        have h := (mR r).mp hr'
        rw [← he,dist_eq_one_iff_adj.mpr hu] at h
        contradiction
      exact two_edges huq (hDq r hr) hne (remote_adj u r hu hr')
    have hsub : insert p (insert v D) ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with e | hm
      · subst x; simp [ph]
      · rcases Finset.mem_insert.mp hm with e | hd'
        · subst x; simp [vh]
        · simp [hnear x hd']
    have hvD : v ∉ D := fun he => by
      have hh := (mR v).mp (hDR he)
      rw [dist_eq_one_iff_adj.mpr hv] at hh
      contradiction
    have hpD : p ∉ insert v D := by
      intro he
      rcases Finset.mem_insert.mp he with eq | hm
      · have hh := (mW p).mp hpW
        rw [eq,dist_eq_one_iff_adj.mpr hv] at hh
        contradiction
      · have hp' := (mW p).mp hpW
        have hp'' := (mR p).mp (hDR hm)
        omega
    have hl := (Finset.card_le_card hsub).trans (distance_two_cap _ hσ u)
    rw [Finset.card_insert_of_notMem hpD,Finset.card_insert_of_notMem hvD] at hl
    omega
  have hcpN : ¬ G.Adj c p := reserve hza hzb hne hab hp (fun e => (hap p hp).mp e rfl)
    ((hap c hcW).mpr hcp) ((hap q hq).mpr hpq.symm) hRb
    (Finset.filter_subset _ _) (fun _ hr => (hyOnly hr).1)
  have hcqN : ¬ G.Adj c q := reserve hzb hza hne.symm (fun e => hab e.symm) hq
    (fun e => (hbq q hq).mp e rfl) ((hbq c hcW).mpr hcq) ((hbq p hp).mpr hpq) hRa
    (Finset.filter_subset _ _) (fun _ hr => (hxOnly hr).1)
  have hcR (r : V) (hr : r ∈ R) : ¬ G.Adj c r := by
    intro he
    rw [← hcoverR] at hr
    rcases Finset.mem_union.mp hr with hX | hY
    · exact hcp ((hxOnly hX).2 c hcW he)
    · exact hcq ((hyOnly hY).2 c hcW he)
  have hsubN : G.neighborFinset c ⊆ ({a,b} : Finset V) := by
    intro x hx
    have hcx := (G.mem_neighborFinset c x).mp hx
    have := h.nonempty
    have hl := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := z) (v := x)).trans hd
    have casesDist : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨ G.dist z x = 3 := by omega
    rcases casesDist with h0 | h1 | h2 | h3
    · have hzx := (h.preconnected z x).dist_eq_zero_iff.mp h0
      subst x
      have hf := (mW c).mp hcW
      rw [dist_eq_one_iff_adj.mpr hcx.symm] at hf
      contradiction
    · exact hZ ▸ (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
    · have hmem := (mW x).mpr h2
      rw [← hWcover] at hmem
      rcases (show x = p ∨ x = q ∨ x = c from by simpa using hmem) with e | e | e
      · exact (hcpN (e ▸ hcx)).elim
      · exact (hcqN (e ▸ hcx)).elim
      · exact (G.ne_of_adj hcx e.symm).elim
    · exact (hcR x ((mR x).mpr h3) hcx).elim
  have hlow := (Finset.card_le_card hsubN).trans Finset.card_le_two
  have hcNe : c ≠ z := by
    intro he
    have hh := (mW c).mp hcW
    simp [he] at hh
  have hhigh := (Graph189Bipartite.degree_pair (G := G) c z hcNe).resolve_right (by omega)
  change G.degree c ≤ 2 at hlow
  omega

#print axioms large_nonadjacent_layout
#print axioms not_order_ten_of_nonadjacent
end Graph189DegreeTwoOuter
