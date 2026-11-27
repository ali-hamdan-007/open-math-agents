import Graph189DistanceLayers
import Graph189BipartiteStructure

namespace Graph189BoundaryHigh
open SimpleGraph Graph189LowDegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

/-- At the first uncovered order, every original degree-(σ+1) vertex
has a good odd-distance nonneighbor. -/
theorem far_good (h : G.Connected) (s : ℕ) (hs : s = G.secondSmallestDegree)
    (hn : Fintype.card V = 2*s+4)
    (hσ : ∀ x, G.distEven x ≤ 1+s) (v : V) (hv : G.degree v = s+1) :
    ∃ w, v ≠ w ∧ 3 ≤ G.dist v w ∧ s ≤ G.degree w ∧
      Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
  let E := Finset.univ.filter (fun w => Even (G.dist v w))
  let O := Finset.univ \ E
  let F := O \ G.neighborFinset v
  have hsub : G.neighborFinset v ⊆ O := by
    intro x hx
    have hd := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v x).mp hx)
    simp [O,E,hd]
  have ho : O.card = Fintype.card V - G.distEven v := by
    unfold O
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    rfl
  have hf : F.card = O.card-G.degree v := Finset.card_sdiff_of_subset hsub
  have hl : 1 < F.card := by have := hσ v; omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hl
  have finalize (w : V) (hw : w ∈ F) (hg : s ≤ G.degree w) :
      v ≠ w ∧ 3 ≤ G.dist v w ∧ s ≤ G.degree w ∧
        Disjoint (G.neighborFinset v) (G.neighborFinset w) := by
    obtain ⟨hwO,hwn⟩ := Finset.mem_sdiff.mp hw
    have hnot : ¬ Even (G.dist v w) := (Finset.mem_sdiff.mp hwO).2 ∘
      (fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    have hne : v ≠ w := by intro he; subst w; exact hnot (by simp)
    have hnon : ¬ G.Adj v w := fun he => hwn ((G.mem_neighborFinset v w).mpr he)
    have hpos : 0 < G.dist v w := h.pos_dist_of_ne hne
    have hone : G.dist v w ≠ 1 := fun he => hnon (dist_eq_one_iff_adj.mp he)
    have htwo : G.dist v w ≠ 2 := fun he => hnot (by rw [he]; decide)
    refine ⟨hne,by omega,hg,?_⟩
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    exact htwo (two_edges ((G.mem_neighborFinset v x).mp hx)
      ((G.mem_neighborFinset w x).mp hy).symm hne hnon)
  rcases Graph189Bipartite.degree_pair (G := G) a b hab with ha' | hb'
  · exact ⟨a,finalize a ha (hs ▸ ha')⟩
  · exact ⟨b,finalize b hb (hs ▸ hb')⟩

omit [DecidableEq V] [Nontrivial V] in
private theorem nbr_mono (hGH : G ≤ H) (x : V) : G.neighborFinset x ⊆ H.neighborFinset x :=
  fun y hy => (H.mem_neighborFinset x y).mpr (hGH ((G.mem_neighborFinset x y).mp hy))

omit [DecidableEq V] [Nontrivial V] in
private theorem deg_mono (hGH : G ≤ H) (x : V) : G.degree x ≤ H.degree x :=
  Finset.card_le_card (nbr_mono hGH x)

/-- A graph saturated under Easwar–Johari's two short-common-neighborhood
closure rules has no unchanged original degree-(σ+1) vertex. -/
theorem raise_middle (h : G.Connected) (s : ℕ) (hs : s = G.secondSmallestDegree)
    (hn : Fintype.card V = 2*s+4) (hσ : ∀ x, G.distEven x ≤ 1+s) (hGH : G ≤ H)
    (sat0 : ∀ x y, x ≠ y → 2*s+1 ≤ H.degree x + H.degree y →
      Disjoint (H.neighborFinset x) (H.neighborFinset y) → H.Adj x y)
    (sat1 : ∀ x y, x ≠ y → 2*s+2 ≤ H.degree x + H.degree y →
      (H.neighborFinset x ∩ H.neighborFinset y).card ≤ 1 → H.Adj x y)
    (sat2 : ∀ x y, x ≠ y → 2*s+3 ≤ H.degree x + H.degree y → H.Adj x y)
    (v : V) (hv : G.degree v = s+1) : s+2 ≤ H.degree v := by
  by_contra! he
  have hmv := deg_mono hGH v
  have hv' : H.degree v = s+1 := by omega
  have heq : G.neighborFinset v = H.neighborFinset v :=
    Finset.eq_of_subset_of_card_le (nbr_mono hGH v) (by
      change H.degree v ≤ G.degree v
      omega)
  obtain ⟨w,hne,hfd,hgw,hd⟩ := far_good h s hs hn hσ v hv
  have hwH := deg_mono hGH w
  have hna : ¬ H.Adj v w := by
    intro hh
    have hm := (H.mem_neighborFinset v w).mpr hh
    rw [← heq] at hm
    have hd := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset v w).mp hm)
    omega
  have cap : (H.neighborFinset v ∩ H.neighborFinset w).card ≤ H.degree w - G.degree w := by
    have hsub : H.neighborFinset v ∩ H.neighborFinset w ⊆ H.neighborFinset w \ G.neighborFinset w := by
      intro x hh
      obtain ⟨hx,hy⟩ := Finset.mem_inter.mp hh
      rw [← heq] at hx
      exact Finset.mem_sdiff.mpr ⟨hy,fun h => Finset.disjoint_left.mp hd hx h⟩
    have hcap := Finset.card_le_card hsub
    rwa [Finset.card_sdiff_of_subset (nbr_mono hGH w)] at hcap
  apply hna
  by_cases h0 : H.degree w = s
  · apply sat0 v w hne (by omega)
    exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp (by omega))
  by_cases h1 : H.degree w = s+1
  · exact sat1 v w hne (by omega) (by omega)
  · exact sat2 v w hne (by omega)


/-- If at most σ+1 original vertices have degree at most σ, the three paper
closure rules force a complete graph at order 2σ+4. -/
theorem complete_of_few_low (h : G.Connected) (s : ℕ) (hs : s = G.secondSmallestDegree)
    (hn : Fintype.card V = 2*s+4) (hσ : ∀ x, G.distEven x ≤ 1+s)
    (hmin : ∀ x, 3 ≤ G.degree x) (hs3 : 3 ≤ s)
    (hfew : (Finset.univ.filter (fun x => G.degree x ≤ s)).card ≤ s+1)
    (hGH : G ≤ H)
    (sat0 : ∀ x y, x ≠ y → 2*s+1 ≤ H.degree x + H.degree y →
      Disjoint (H.neighborFinset x) (H.neighborFinset y) → H.Adj x y)
    (sat1 : ∀ x y, x ≠ y → 2*s+2 ≤ H.degree x + H.degree y →
      (H.neighborFinset x ∩ H.neighborFinset y).card ≤ 1 → H.Adj x y)
    (sat2 : ∀ x y, x ≠ y → 2*s+3 ≤ H.degree x + H.degree y → H.Adj x y) :
    H = ⊤ := by
  let U := Finset.univ.filter (fun x => s < G.degree x)
  let C := Finset.univ.filter (fun x => s ≤ G.degree x)
  have hU : s+3 ≤ U.card := by
    have he : U = Finset.univ \ (Finset.univ.filter (fun x => G.degree x ≤ s)) := by
      ext x
      simp [U]
    rw [he,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,hn]
    omega
  have hg (x : V) (hx : x ∈ U) : s+2 ≤ H.degree x := by
    have hh := (Finset.mem_filter.mp hx).2
    by_cases e : G.degree x = s+1
    · exact raise_middle h s hs hn hσ hGH sat0 sat1 sat2 x e
    · have := deg_mono hGH x
      omega
  have countNeighbors (x : V) (A : Finset V)
      (hA : ∀ y ∈ A, x ≠ y → H.Adj x y) : A.card ≤ H.degree x + 1 := by
    have hsub : A ⊆ insert x (H.neighborFinset x) := by
      intro y hy
      by_cases he : y = x
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert_of_mem ((H.mem_neighborFinset x y).mpr (hA y hy (Ne.symm he)))
    have hp := (Finset.card_le_card hsub).trans (Finset.card_insert_le x (H.neighborFinset x))
    exact hp
  have hC : Fintype.card V ≤ C.card+1 := by
    have hsC : (Finset.univ \ C).card ≤ 1 := by
      refine Finset.card_le_one.mpr ?_
      intro x hx y hy
      by_contra he
      have hg := Graph189Bipartite.degree_pair (G := G) x y he
      have ha : ¬ s ≤ G.degree x := fun h => (Finset.mem_sdiff.mp hx).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      have hb : ¬ s ≤ G.degree y := fun h => (Finset.mem_sdiff.mp hy).2
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      rw [← hs] at hg
      exact hg.elim ha hb
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    rw [Finset.card_univ] at hh
    omega
  suffices high : ∀ x ∈ U, s+3 ≤ H.degree x by
    have cHigh (x : V) (hx : x ∈ C) : s+3 ≤ H.degree x := by
      have hgood : s ≤ H.degree x := ((Finset.mem_filter.mp hx).2).trans (deg_mono hGH x)
      by_cases hxU : x ∈ U
      · exact high x hxU
      · have hh : U ⊆ H.neighborFinset x := by
          intro y hy
          exact (H.mem_neighborFinset x y).mpr
            (sat2 x y (fun e => hxU (e.symm ▸ hy)) (by have := high y hy; omega))
        exact hU.trans (Finset.card_le_card hh)
    have everyGood (x : V) (hx : x ∈ C) (y : V) (hne : x ≠ y) : H.Adj x y := by
      have hxdeg := countNeighbors x C (fun v hv hne =>
        sat2 x v hne (by have := cHigh x hx; have := cHigh v hv; omega))
      have hydeg := (hmin y).trans (deg_mono hGH y)
      exact sat2 x y hne (by omega)
    apply le_antisymm le_top
    intro x y hxy
    have hh := Graph189Bipartite.degree_pair (G := G) x y hxy.ne
    rw [← hs] at hh
    exact hh.elim
      (fun hx => everyGood x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩) y hxy.ne)
      (fun hy => (everyGood y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩) x hxy.ne.symm).symm)

  have Uclique (x y : V) (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) : H.Adj x y :=
    sat2 x y hxy (by have := hg x hx; have := hg y hy; omega)
  by_cases hBig : s+4 ≤ U.card
  · intro x hx
    have hh := countNeighbors x U (fun y hy hxy => Uclique x y hx hy hxy)
    omega
  have hSize : U.card = s+3 := by omega
  by_cases added : ∃ x ∈ C, x ∉ U ∧ s+1 ≤ H.degree x
  · obtain ⟨x,hxC,hxU,hxD⟩ := added
    intro u hu
    have hc := countNeighbors u (insert x U) (by
      intro y hy hne
      rcases Finset.mem_insert.mp hy with e | hy
      · subst y
        exact sat2 u x hne (by have := hg u hu; omega)
      · exact Uclique u y hu hy hne)
    rw [Finset.card_insert_of_notMem hxU,hSize] at hc
    omega
  have original (x : V) (hxC : x ∈ C) (hxU : x ∉ U) :
      G.degree x = s ∧ G.neighborFinset x = H.neighborFinset x := by
    have h1 := (Finset.mem_filter.mp hxC).2
    have h2 : ¬ s < G.degree x := fun he => hxU (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
    have h3 : ¬ s+1 ≤ H.degree x := fun he => added ⟨x,hxC,hxU,he⟩
    have heq : G.degree x = s := by omega
    exact ⟨heq,Finset.eq_of_subset_of_card_le (nbr_mono hGH x) (by
      change H.degree x ≤ G.degree x
      omega)⟩
  obtain ⟨x,hxC,hxU⟩ : ∃ x ∈ C, x ∉ U := by
    by_contra! he
    have hle := Finset.card_le_card (show C ⊆ U from he)
    omega
  obtain ⟨u,hu⟩ : U.Nonempty := Finset.card_pos.mp (by omega)
  have cross {a b : V} (p : G.Walk a b) (ha : a ∈ U) (hb : b ∉ U) :
      ∃ r ∈ U, ∃ t ∉ U, G.Adj r t := by
    induction p with
    | nil => exact (hb ha).elim
    | @cons a w b haw p ih =>
      by_cases hw : w ∈ U
      · exact ih hw hb
      · exact ⟨a,ha,w,hw,haw⟩
  obtain ⟨p⟩ := h.preconnected u x
  obtain ⟨q,hq,t,ht,hqt⟩ := cross p hu hxU
  have hqD : s+3 ≤ H.degree q := by
    have hh := countNeighbors q (insert t U) (by
      intro y hy hne
      rcases Finset.mem_insert.mp hy with e | hy
      · exact e.symm ▸ hGH hqt
      · exact Uclique q y hq hy hne)
    rw [Finset.card_insert_of_notMem ht,hSize] at hh
    omega
  have qGood (v : V) (hvC : v ∈ C) (hvU : v ∉ U) : G.Adj v q := by
    have hne : v ≠ q := fun eq => hvU (eq.symm ▸ hq)
    have hvD := (Finset.mem_filter.mp hvC).2.trans (deg_mono hGH v)
    apply (G.mem_neighborFinset v q).mp
    rw [(original v hvC hvU).2]
    exact (H.mem_neighborFinset v q).mpr (sat2 v q hne (by omega))
  have two (y : V) (hyC : y ∈ C) (hxy : x ≠ y) (hna : ¬ G.Adj x y) :
      G.dist x y = 2 := by
    obtain ⟨hxD,hxEq⟩ := original x hxC hxU
    by_cases hyU : y ∈ U
    · have hyH := hg y hyU
      have hyG : s+1 ≤ G.degree y := by have := (Finset.mem_filter.mp hyU).2; omega
      have hnaH : ¬ H.Adj x y := by
        intro hh
        have hm := (H.mem_neighborFinset x y).mpr hh
        rw [← hxEq] at hm
        exact hna ((G.mem_neighborFinset x y).mp hm)
      have hxH : H.degree x = s := by
        have hh := congrArg Finset.card hxEq
        change G.degree x = H.degree x at hh
        omega
      have hyExact : H.degree y = s+2 := by
        by_contra he
        exact hnaH (sat2 x y hxy (by omega))
      have hCommon : 1 < (H.neighborFinset x ∩ H.neighborFinset y).card := by
        by_contra! he
        exact hnaH (sat1 x y hxy (by omega) he)
      have cap : (H.neighborFinset y \ G.neighborFinset y).card ≤ 1 := by
        rw [Finset.card_sdiff_of_subset (nbr_mono hGH y)]
        change H.degree y - G.degree y ≤ 1
        omega
      have exists_old : ∃ w ∈ H.neighborFinset x ∩ H.neighborFinset y, w ∈ G.neighborFinset y := by
        by_contra! he
        have hsub : H.neighborFinset x ∩ H.neighborFinset y ⊆ H.neighborFinset y \ G.neighborFinset y := by
          intro z hz
          exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hz).2,he z hz⟩
        have := Finset.card_le_card hsub
        omega
      obtain ⟨w,hw,hyw⟩ := exists_old
      have hxw := (Finset.mem_inter.mp hw).1
      rw [← hxEq] at hxw
      exact two_edges ((G.mem_neighborFinset x w).mp hxw) ((G.mem_neighborFinset y w).mp hyw).symm hxy hna
    · exact two_edges (qGood x hxC hxU) (qGood y hyC hyU).symm hxy hna
  let K := C \ insert x (G.neighborFinset x)
  have hK : s+2 ≤ K.card := by
    have he := Finset.le_card_sdiff (insert x (G.neighborFinset x)) C
    have hf := Finset.card_insert_le x (G.neighborFinset x)
    have hg : G.degree x = s := (original x hxC hxU).1
    change (insert x (G.neighborFinset x)).card ≤ G.degree x + 1 at hf
    change C.card - (insert x (G.neighborFinset x)).card ≤ K.card at he
    omega
  have hSub : K ⊆ Finset.univ.filter (fun v => Even (G.dist x v)) := by
    intro y hy
    obtain ⟨hyC,hy'⟩ := Finset.mem_sdiff.mp hy
    have hne : x ≠ y := fun e => hy' (Finset.mem_insert.mpr (Or.inl e.symm))
    have hna : ¬ G.Adj x y := fun h => hy'
      (Finset.mem_insert_of_mem ((G.mem_neighborFinset x y).mpr h))
    have ht := two y hyC hne hna
    simp [ht]
  have hh := Finset.card_le_card hSub
  change K.card ≤ G.distEven x at hh
  have := hσ x
  omega

#print axioms far_good
#print axioms raise_middle
#print axioms complete_of_few_low
end Graph189BoundaryHigh
