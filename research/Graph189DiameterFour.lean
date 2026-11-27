import Graph189DistanceLayers
import Graph189BipartiteStructure

namespace Graph189DiameterFour
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def layer (G : SimpleGraph V) (x : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun v => G.dist x v = r

noncomputable def ties (G : SimpleGraph V) (x y : V) (r : ℕ) : Finset V :=
  layer G x r ∩ layer G y r

omit [DecidableEq V] in
theorem mem_layer (x : V) (r : ℕ) (v : V) : v ∈ layer G x r ↔ G.dist x v = r := by
  simp [layer]

theorem mem_ties (x y : V) (r : ℕ) (v : V) :
    v ∈ ties G x y r ↔ G.dist x v = r ∧ G.dist y v = r := by
  simp [ties, mem_layer]

/-- In diameter at most four, the exact even-distance budget is spent on
the second and fourth layers together, in addition to the base vertex. -/
theorem even_layers_four (h : G.Connected) (hd : G.diam ≤ 4) (x : V) :
    G.distEven x = 1 + (layer G x 2).card + (layer G x 4).card := by
  have := h.nonempty
  have hU : (Finset.univ.filter (fun v => Even (G.dist x v))) =
      ({x} : Finset V) ∪ layer G x 2 ∪ layer G x 4 := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_singleton,
      mem_layer,Nat.even_iff]
    have hlim := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := v)).trans hd
    have hz := (h.preconnected x v).dist_eq_zero_iff
    constructor
    · intro he
      by_cases hv : v = x
      · exact Or.inl (Or.inl hv)
      · have hne : G.dist x v ≠ 0 := fun h0 => hv (hz.mp h0).symm
        omega
    · intro he
      rcases he with (rfl | he) | he
      · simp
      · omega
      · omega
  have hdis₂ : Disjoint ({x} : Finset V) (layer G x 2) := by
    simp [mem_layer]
  have hdis₄ : Disjoint (({x} : Finset V) ∪ layer G x 2) (layer G x 4) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hv'
    have h4 := (mem_layer x 4 v).mp hv'
    rcases Finset.mem_union.mp hv with e | e
    · have eq : v = x := by simpa using e
      subst v
      simp at h4
    · have h2 := (mem_layer x 2 v).mp e
      omega
  rw [distEven,hU,Finset.card_union_of_disjoint hdis₄,
    Finset.card_union_of_disjoint hdis₂,Finset.card_singleton]

/-- Distance-four endpoints spend additional even-distance budget on each
neighbor of the opposite endpoint which does not lie at distance three. -/
theorem opposite_predecessor_lower [DecidableRel G.Adj] (h : G.Connected)
    (hd : G.diam ≤ 4) {x y : V} (hxy : G.dist x y = 4)
    (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) :
    G.degree y + (layer G x 2).card + 1 ≤
      G.secondSmallestDegree + ((G.neighborFinset y) ∩ layer G x 3).card := by
  have := h.nonempty
  let B := G.neighborFinset y
  let P := B ∩ layer G x 3
  let Q := B ∩ layer G x 4
  have hB : B = P ∪ Q := by
    ext v
    simp only [P,Q,Finset.mem_union,Finset.mem_inter,mem_layer]
    constructor
    · intro hv
      have hadj := (G.mem_neighborFinset y v).mp hv
      have htri := h.dist_triangle (u := x) (v := v) (w := y)
      rw [hxy,dist_eq_one_iff_adj.mpr hadj.symm] at htri
      have hlim := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp h) (u := x) (v := v)).trans hd
      have hh : G.dist x v = 3 ∨ G.dist x v = 4 := by omega
      exact hh.imp (fun he => ⟨hv,he⟩) (fun he => ⟨hv,he⟩)
    · exact fun h => h.elim And.left And.left
  have hdis : Disjoint P Q := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hv'
    have h3 := (mem_layer x 3 v).mp (Finset.mem_inter.mp hv).2
    have h4 := (mem_layer x 4 v).mp (Finset.mem_inter.mp hv').2
    omega
  have hcard : G.degree y = P.card + Q.card := by
    change B.card = _
    rw [hB,Finset.card_union_of_disjoint hdis]
  have hyQ : y ∉ Q := by simp [Q,B]
  have hq : insert y Q ⊆ layer G x 4 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with e | e
    · exact (mem_layer x 4 v).mpr (e.symm ▸ hxy)
    · exact (Finset.mem_inter.mp e).2
  have hle := Finset.card_le_card hq
  rw [Finset.card_insert_of_notMem hyQ] at hle
  have hbound := hσ x
  rw [even_layers_four h hd x] at hbound
  change G.degree y + (layer G x 2).card + 1 ≤ G.secondSmallestDegree + P.card
  omega


/-- A diameter-four graph's order is controlled by odd ties at distances one
and three across an edge, with a penalty for even ties at distances two and four. -/
theorem edge_tie_budget [DecidableRel G.Adj] (h : G.Connected) (hd : G.diam ≤ 4)
    {x y : V} (hxy : G.Adj x y) (hσ : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) :
    Fintype.card V + (ties G x y 2).card + (ties G x y 4).card ≤
      2 * (1 + G.secondSmallestDegree) + (ties G x y 1).card + (ties G x y 3).card := by
  have := h.nonempty
  let Ex := Finset.univ.filter (fun v => Even (G.dist x v))
  let Ey := Finset.univ.filter (fun v => Even (G.dist y v))
  have bounds (v : V) : G.dist x v ≤ 4 ∧ G.dist y v ≤ 4 := by
    have hf := G.connected_iff_ediam_ne_top.mp h
    exact ⟨(G.dist_le_diam hf).trans hd,(G.dist_le_diam hf).trans hd⟩
  have delta (v : V) :
      G.dist x v ≤ G.dist y v + 1 ∧ G.dist y v ≤ G.dist x v + 1 := by
    have hx := h.dist_triangle (u := x) (v := y) (w := v)
    have hy := h.dist_triangle (u := y) (v := x) (w := v)
    rw [dist_eq_one_iff_adj.mpr hxy] at hx
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at hy
    omega
  have nz (v : V) : ¬ (G.dist x v = 0 ∧ G.dist y v = 0) := by
    rintro ⟨hx,hy⟩
    exact hxy.ne (((h.preconnected x v).dist_eq_zero_iff.mp hx).trans
      ((h.preconnected y v).dist_eq_zero_iff.mp hy).symm)
  have he : Ex ∩ Ey = ties G x y 2 ∪ ties G x y 4 := by
    ext v
    simp only [Ex,Ey,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,
      Nat.even_iff,Finset.mem_union, mem_ties]
    have ⟨hb1,hb2⟩ := bounds v
    have ⟨hc1,hc2⟩ := delta v
    have hn := nz v
    omega
  have ho : (Finset.univ \ (Ex ∪ Ey)) = ties G x y 1 ∪ ties G x y 3 := by
    ext v
    simp only [Ex,Ey,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and,
      Nat.even_iff,Finset.mem_union, mem_ties]
    have ⟨hb1,hb2⟩ := bounds v
    have ⟨hc1,hc2⟩ := delta v
    omega
  have hdis {r s : ℕ} (hrs : r ≠ s) : Disjoint (ties G x y r) (ties G x y s) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv hv'
    exact hrs (((mem_ties x y r v).mp hv).1.symm.trans ((mem_ties x y s v).mp hv').1)
  have hI := Finset.card_union_add_card_inter Ex Ey
  rw [he,Finset.card_union_of_disjoint (hdis (by decide : 2 ≠ 4))] at hI
  have hO := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Ex ∪ Ey))
  rw [ho,Finset.card_union_of_disjoint (hdis (by decide : 1 ≠ 3)),Finset.card_univ] at hO
  change (Ex ∪ Ey).card + _ = G.distEven x + G.distEven y at hI
  have hx := hσ x
  have hy := hσ y
  omega

#print axioms even_layers_four
#print axioms opposite_predecessor_lower
#print axioms edge_tie_budget
end Graph189DiameterFour
