import Graph189WedgeOrder

open SimpleGraph Finset
namespace Graph189ColumnCancel

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem switch (A B : Finset V) (r : V → V → Prop) [DecidableRel r] :
    (∑ a ∈ A, (B.filter (fun b => r a b)).card) =
      ∑ b ∈ B, (A.filter (fun a => r a b)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

omit [Fintype V] [DecidableEq V] in
/-- Finite incidence cancellation with the three original graph vertex layers. -/
theorem cancel {G : SimpleGraph V} [DecidableRel G.Adj] (A B C : Finset V) (k w : ℕ)
    (row : ∀ a ∈ A, (C.filter (fun y => G.dist a y = 2)).card +
        (B.filter (fun b => G.dist a b ≤ 2)).card ≤ k)
    (col : ∀ b ∈ B, (C.filter (fun y => G.Adj b y)).card ≤
        (A.filter (fun a => G.dist a b ≤ 2)).card)
    (width : ∀ y ∈ C, w ≤ (A.filter (fun a => G.dist a y = 2)).card +
        (B.filter (fun b => G.Adj b y)).card) :
    w * C.card ≤ k * A.card := by
  classical
  have h := sum_le_sum width
  have r := sum_le_sum row
  have c := sum_le_sum col
  rw [sum_add_distrib] at h r
  rw [←switch A C (fun a y => G.dist a y = 2), ←switch B C G.Adj] at h
  rw [←switch A B (fun a b => G.dist a b ≤ 2)] at c
  simpa [Nat.mul_comm] using (show C.card * w ≤ A.card * k by
    simp only [sum_const, smul_eq_mul] at h r
    omega)

variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem pair_cap (D E : Finset V) (hDE : Disjoint D E) {u : V} {k : ℕ}
    (hd : ∀ v ∈ D, G.dist u v = 2) (he : ∀ v ∈ E, G.dist u v = 2)
    (cap : G.distEven u ≤ k+1) : D.card + E.card ≤ k := by
  classical
  let pos := (univ.filter (fun v => Even (G.dist u v))).erase u
  have hpos : pos.card ≤ k := by
    change (univ.filter (fun v => Even (G.dist u v))).card ≤ k+1 at cap
    have hself : u ∈ univ.filter (fun v => Even (G.dist u v)) := by simp
    dsimp [pos]
    rw [card_erase_of_mem hself]
    omega
  have sub : D ∪ E ⊆ pos := by
    intro v hv
    have two : G.dist u v = 2 := (mem_union.mp hv).elim (hd v) (he v)
    have ne : v ≠ u := by rintro rfl; simp at two
    exact mem_erase.mpr ⟨ne,mem_filter.mpr ⟨mem_univ _,by rw [two]; decide⟩⟩
  have h := (card_le_card sub).trans hpos
  rwa [card_union_of_disjoint hDE] at h

/-- Every actual second-layer column pays its entire third-layer incidence. -/
theorem column (hc : G.Connected) (x b u : V) (C : Finset V) {k : ℕ}
    (root : k ≤ G.degree x) (pred₁ : G.Adj x u) (pred₂ : G.Adj u b)
    (layer : ∀ y ∈ C, G.dist x y = 3) (cap : G.distEven u ≤ k+1) :
    (C.filter (fun y => G.Adj b y)).card + (G.degree x-k) ≤
       ((G.neighborFinset x).filter (fun a => G.dist a b ≤ 2)).card := by
  classical
  let A := G.neighborFinset x
  let D := A.filter (fun a => G.dist u a = 2)
  let E := C.filter (fun y => G.Adj b y)
  have near (a : V) (ha : a ∈ A) : G.dist x a = 1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp ha)
  have one := dist_eq_one_iff_adj.mpr pred₁
  have ub := dist_eq_one_iff_adj.mpr pred₂
  have dd : Disjoint D E := by
    rw [Finset.disjoint_left]
    intro v hv hy
    have h₁ := near _ (mem_filter.mp hv).1
    have h₂ := layer _ (mem_filter.mp hy).1
    omega
  have cp := pair_cap (G:=G) D E dd (fun _ h => (mem_filter.mp h).2) (by
    intro y hy
    obtain ⟨hy,hby⟩ := mem_filter.mp hy
    have hxy := layer _ hy
    have low := hc.dist_triangle (u:=x) (v:=u) (w:=y)
    have up := hc.dist_triangle (u:=u) (v:=b) (w:=y)
    rw [ub,dist_eq_one_iff_adj.mpr hby] at up
    omega) cap
  have sub : A.filter (fun a => ¬G.dist u a = 2) ⊆
      A.filter (fun a => G.dist a b ≤ 2) := by
    intro a ha
    obtain ⟨ha,hne⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨ha,?_⟩
    have hux := dist_eq_one_iff_adj.mpr pred₁.symm
    have up := hc.dist_triangle (u:=u) (v:=x) (w:=a)
    have up' := hc.dist_triangle (u:=a) (v:=u) (w:=b)
    rw [show G.dist a u = G.dist u a from SimpleGraph.dist_comm] at up'
    have hxa := near a ha
    omega
  have part := A.card_filter_add_card_filter_not (fun a => G.dist u a = 2)
  have cardA : A.card = G.degree x := G.card_neighborFinset_eq_degree x
  have bound := card_le_card sub
  change D.card + _ = _ at part
  change E.card + _ ≤ (A.filter _).card
  omega


/-- At a maximum-degree root, its missing first-layer neighbors pay for every
direct neighbor in the second layer; the remaining incidences debit even pairs. -/
theorem row_bound (hc : G.Connected) (x a : V) (B C : Finset V) {k : ℕ}
    (hxa : G.Adj x a) (maxd : G.degree a ≤ G.degree x)
    (hB : ∀ b ∈ B, G.dist x b = 2) (hC : ∀ y ∈ C, G.dist x y = 3)
    (cap : G.distEven a ≤ k+1) :
    (C.filter (fun y => G.dist a y = 2)).card +
      (B.filter (fun b => G.dist a b ≤ 2)).card ≤ k := by
  classical
  let A := G.neighborFinset x
  let D := A.filter (fun v => G.dist a v = 2)
  let N := A.filter (fun v => ¬G.dist a v = 2)
  let T := B.filter (fun v => G.dist a v ≤ 2)
  let P := T.filter (fun v => G.dist a v = 2)
  let Q := T.filter (fun v => ¬G.dist a v = 2)
  let Y := C.filter (fun v => G.dist a v = 2)
  have near (v : V) (h : v ∈ A) : G.dist x v = 1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h)
  have hax := dist_eq_one_iff_adj.mpr hxa.symm
  have bd (v : V) (h : v ∈ Q) : G.dist x v = 2 :=
    hB _ (mem_filter.mp (mem_filter.mp h).1).1
  have ad (v : V) (h : v ∈ N.erase a) : G.dist x v = 1 :=
    near _ (mem_filter.mp (mem_erase.mp h).2).1
  have disj : Disjoint (N.erase a) Q := by
    rw [Finset.disjoint_left]
    intro v hv hq
    have := ad _ hv
    have := bd _ hq
    omega
  have nx : x ∉ N.erase a ∪ Q := by
    intro h
    rcases mem_union.mp h with h|h
    · simpa using ad _ h
    · simpa using bd _ h
  have sub : insert x (N.erase a ∪ Q) ⊆ G.neighborFinset a := by
    intro v hv
    apply (G.mem_neighborFinset _ _).mpr
    rcases mem_insert.mp hv with rfl|hv
    · exact hxa.symm
    apply dist_eq_one_iff_adj.mp
    rcases mem_union.mp hv with hv|hv
    · have h₂ := (mem_filter.mp (mem_erase.mp hv).2).2
      have h₃ := hc.dist_triangle (u:=a) (v:=x) (w:=v)
      have h₄ := ad _ hv
      have hz : G.dist a v ≠ 0 := fun eq => (mem_erase.mp hv).1 (hc.dist_eq_zero_iff.mp eq).symm
      omega
    · have h₂ := (mem_filter.mp hv).2
      have h₃ := (mem_filter.mp (mem_filter.mp hv).1).2
      have h₄ := bd _ hv
      have h₅ := dist_eq_one_iff_adj.mpr hxa
      have hz : G.dist a v ≠ 0 := by
        intro eq
        have id := hc.dist_eq_zero_iff.mp eq
        subst v
        omega
      omega
  have size := card_le_card sub
  rw [card_insert_of_notMem nx, card_union_of_disjoint disj, G.card_neighborFinset_eq_degree] at size
  have haN : a ∈ N := mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr hxa, by simp⟩
  have erased := card_erase_add_one haN
  have partA : D.card + N.card = A.card := A.card_filter_add_card_filter_not _
  have cA : A.card = G.degree x := G.card_neighborFinset_eq_degree x
  have qd : Q.card ≤ D.card := by omega
  have dp : Disjoint D P := by
    rw [Finset.disjoint_left]
    intro v hv hp
    have h₁ := near _ (mem_filter.mp hv).1
    have h₂ := hB _ (mem_filter.mp (mem_filter.mp hp).1).1
    omega
  have dy : Disjoint (D ∪ P) Y := by
    rw [Finset.disjoint_left]
    intro v hp hy
    have h₃ := hC _ (mem_filter.mp hy).1
    rcases mem_union.mp hp with hv|hv
    · have h₁ := near _ (mem_filter.mp hv).1
      omega
    · have h₂ := hB _ (mem_filter.mp (mem_filter.mp hv).1).1
      omega
  have three := pair_cap (G:=G) (D ∪ P) Y dy (by
    intro v hv
    rcases mem_union.mp hv with hv|hv
    · exact (mem_filter.mp hv).2
    · exact (mem_filter.mp hv).2) (fun _ hv => (mem_filter.mp hv).2) cap
  rw [card_union_of_disjoint dp] at three
  have partT : P.card + Q.card = T.card := T.card_filter_add_card_filter_not _
  change Y.card + T.card ≤ k
  omega

theorem full_column_cancellation (hc : G.Connected) (x : V) (B C : Finset V) {k w : ℕ}
    (hmax : ∀ a, G.degree a ≤ G.degree x) (large : k ≤ G.degree x)
    (hB : ∀ b ∈ B, G.dist x b = 2)
    (pred : ∀ b ∈ B, ∃ u, G.Adj x u ∧ G.Adj u b)
    (hC : ∀ y ∈ C, G.dist x y = 3) (cap : ∀ a, G.distEven a ≤ k+1)
    (width : ∀ y ∈ C, w ≤ ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
        (B.filter (fun b => G.Adj b y)).card) :
    w * C.card ≤ k * G.degree x := by
  rw [←G.card_neighborFinset_eq_degree]
  apply cancel _ _ _ _ _ _ _ width
  · intro a ha
    exact row_bound hc x a B C ((G.mem_neighborFinset _ _).mp ha) (hmax a) hB hC (cap a)
  · intro b hb
    obtain ⟨u,hu,hub⟩ := pred b hb
    have H := column hc x b u C large hu hub hC (cap u)
    omega


/-- A bound on the two common-neighbor terms of actual geodesics gives the
width consumed in the cancellation. -/
theorem geodesic_cost (hc : G.Connected) (x i j y : V) (B : Finset V)
    (allB : ∀ b, G.dist x b = 2 → b ∈ B)
    (hxi : G.Adj x i) (_hij : G.Adj i j) (hjy : G.Adj j y) (far : G.dist x y = 3) :
    (G.neighborFinset x ∩ G.neighborFinset j).card +
      (G.neighborFinset y ∩ G.neighborFinset i).card ≤
        ((G.neighborFinset x).filter (fun a => G.dist a y = 2)).card +
          (B.filter (fun b => G.Adj b y)).card := by
  apply Nat.add_le_add
  · apply card_le_card
    intro a ha
    obtain ⟨hxa,hja⟩ := mem_inter.mp ha
    refine mem_filter.mpr ⟨hxa,?_⟩
    have lower := hc.dist_triangle (u:=x) (v:=a) (w:=y)
    have upper := hc.dist_triangle (u:=a) (v:=j) (w:=y)
    have xa := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hxa)
    have aj := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hja).symm
    have jy := dist_eq_one_iff_adj.mpr hjy
    omega
  · apply card_le_card
    intro b hb
    obtain ⟨hyb,hib⟩ := mem_inter.mp hb
    have byedge := ((G.mem_neighborFinset _ _).mp hyb).symm
    refine mem_filter.mpr ⟨allB b ?_,byedge⟩
    have lower := hc.dist_triangle (u:=x) (v:=b) (w:=y)
    have upper := hc.dist_triangle (u:=x) (v:=i) (w:=b)
    have xi := dist_eq_one_iff_adj.mpr hxi
    have ib := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hib)
    have bdist := dist_eq_one_iff_adj.mpr byedge
    omega

#print axioms geodesic_cost
#print axioms full_column_cancellation

#print axioms cancel
#print axioms column
end Graph189ColumnCancel
