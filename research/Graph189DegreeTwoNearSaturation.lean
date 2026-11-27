import Graph189DegreeTwoAdjacent

namespace Graph189DegreeTwoNearSaturation
open SimpleGraph Graph189LowDegreeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An exclusive remote vertex must have a neighbor across the remote partition
if its own side, the overlap, and its unique middle-layer neighbor are too small. -/
theorem exclusive_cross_edge (s : ℕ) (hs : 4 ≤ s) (P Q T : Finset V)
    (hP : P.card = s - 2) (hT : T.card ≤ 1) {p r : V} (hr : r ∈ P)
    (hdeg : s ≤ G.degree r)
    (hNbr : G.neighborFinset r ⊆ insert p (P ∪ Q ∪ T)) :
    ∃ q ∈ Q, G.Adj r q := by
  by_contra! hn
  have hsub : G.neighborFinset r ⊆ insert p ((P.erase r) ∪ T) := by
    intro x hx
    rcases Finset.mem_insert.mp (hNbr hx) with he | hmem
    · exact Finset.mem_insert.mpr (Or.inl he)
    · rcases Finset.mem_union.mp hmem with hm | ht
      · rcases Finset.mem_union.mp hm with hp | hq
        · have hne := G.ne_of_adj ((G.mem_neighborFinset r x).mp hx)
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (Finset.mem_erase.mpr ⟨hne.symm,hp⟩))
        · exact (hn x hq ((G.mem_neighborFinset r x).mp hx)).elim
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ ht)
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_insert_le p ((P.erase r) ∪ T)
  have h₃ := Finset.card_union_le (P.erase r) T
  rw [Finset.card_erase_of_mem hr,hP] at h₃
  change s ≤ (G.neighborFinset r).card at hdeg
  omega

/-- If the exclusive remote vertices already fill all but two distance-two
slots, a middle-layer vertex must see the entire shared part. -/
theorem sees_shared_part (s : ℕ) (hs : 4 ≤ s)
    (hCap : ∀ u : V, (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s)
    {p a b z : V} (S X : Finset V) (hS : S.card = s - 2) (hX : X.card = s - 2)
    (hSX : Disjoint S X) (hzS : z ∉ S) (hzX : z ∉ X)
    (haS : a ∉ S) (haX : a ∉ X) (haz : a ≠ z)
    (hpa : ¬ G.Adj p a) (hpaNe : p ≠ a) (hpb : G.Adj p b)
    (hpS : p ∉ S) (hSanchor : ∀ c ∈ S, G.Adj a c ∧ G.Adj b c)
    (hz : G.dist p z = 2) (hnear : ∀ x ∈ X, G.dist p x = 2) :
    ∀ c ∈ S, G.Adj p c := by
  let M := S.filter (fun c => ¬ G.Adj p c)
  let D := Finset.univ.filter (fun x => G.dist p x = 2)
  have hmS : M ⊆ S := Finset.filter_subset _ _
  have hmX : Disjoint X M :=
    Finset.disjoint_left.mpr (fun x hx hm => Finset.disjoint_left.mp hSX (hmS hm) hx)
  have hzXM : z ∉ X ∪ M := fun h =>
    (Finset.mem_union.mp h).elim hzX (fun h => hzS (hmS h))
  have haXM : a ∉ X ∪ M := fun h =>
    (Finset.mem_union.mp h).elim haX (fun h => haS (hmS h))
  have first : insert z (X ∪ M) ⊆ D := by
    intro x hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hmem with e | hm
    · exact e.symm ▸ hz
    · rcases Finset.mem_union.mp hm with hx | hm
      · exact hnear x hx
      · obtain ⟨hxS,hpx⟩ := Finset.mem_filter.mp hm
        exact two_edges hpb (hSanchor x hxS).2 (fun e => hpS (e.symm ▸ hxS)) hpx
  have hb := (Finset.card_le_card first).trans (hCap p)
  rw [Finset.card_insert_of_notMem hzXM,Finset.card_union_of_disjoint hmX,hX] at hb
  have hSmall : M.card ≤ 1 := by omega
  obtain ⟨c,hc,hpc⟩ : ∃ c ∈ S, G.Adj p c := by
    by_contra! hn
    have hsub : S ⊆ M := fun x hx => Finset.mem_filter.mpr ⟨hx,hn x hx⟩
    have hle := Finset.card_le_card hsub
    omega
  have hpaTwo : G.dist p a = 2 := two_edges hpc (hSanchor c hc).1.symm hpaNe hpa
  have second : insert a (insert z (X ∪ M)) ⊆ D := by
    intro x hm
    rcases Finset.mem_insert.mp hm with e | hh
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.symm ▸ hpaTwo⟩
    · exact first hh
  have haZ : a ∉ insert z (X ∪ M) := fun hh =>
    (Finset.mem_insert.mp hh).elim haz haXM
  have hl := (Finset.card_le_card second).trans (hCap p)
  rw [Finset.card_insert_of_notMem haZ,Finset.card_insert_of_notMem hzXM,
    Finset.card_union_of_disjoint hmX,hX] at hl
  have hzM : M = ∅ := Finset.card_eq_zero.mp (by omega)
  intro c hc
  by_contra h
  have hh : c ∈ M := Finset.mem_filter.mpr ⟨hc,h⟩
  simp [hzM] at hh

omit [DecidableRel G.Adj] in
/-- The shared middle layer cannot have all of both exclusive remote classes
at distance two. This proves the final contradiction in the overlap case. -/
theorem shared_excessive (s : ℕ) (hs : 4 ≤ s)
    (hCap : ∀ u : V, (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s)
    {c p q z : V} (X Y : Finset V) (hX : X.card = s - 2) (hY : Y.card = s - 2)
    (hXY : Disjoint X Y) (hzX : z ∉ X) (hzY : z ∉ Y)
    (hcX : c ∉ X) (hcY : c ∉ Y)
    (hcp : G.Adj c p) (hcq : G.Adj c q) (hcz : G.dist c z = 2)
    (hpX : ∀ r ∈ X, G.Adj p r ∧ ¬ G.Adj c r)
    (hqY : ∀ r ∈ Y, G.Adj q r ∧ ¬ G.Adj c r) : False := by
  have hzU : z ∉ X ∪ Y := fun he => (Finset.mem_union.mp he).elim hzX hzY
  have hf : insert z (X ∪ Y) ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
    intro r hr
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hr with he | hm
    · exact he.symm ▸ hcz
    · rcases Finset.mem_union.mp hm with hm | hm
      · obtain ⟨hpr,hcr⟩ := hpX r hm
        exact two_edges hcp hpr (fun e => hcX (e.symm ▸ hm)) hcr
      · obtain ⟨hqr,hcr⟩ := hqY r hm
        exact two_edges hcq hqr (fun e => hcY (e.symm ▸ hm)) hcr
  have hle := (Finset.card_le_card hf).trans (hCap c)
  rw [Finset.card_insert_of_notMem hzU,Finset.card_union_of_disjoint hXY,hX,hY] at hle
  omega


/-- The case of one overlapping remote vertex is impossible. Here P and Q
are the two exclusive remote classes, T is their common residual class, and
S is the shared middle layer. -/
theorem overlap_impossible (s : ℕ) (hs : 4 ≤ s)
    (hCap : ∀ u : V, (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s)
    (S P Q T : Finset V) (hS : S.card = s - 2)
    (hP : P.card = s - 2) (hQ : Q.card = s - 2) (hT : T.card ≤ 1)
    (hSP : Disjoint S P) (hSQ : Disjoint S Q) (hPQ : Disjoint P Q)
    (z a b p q : V)
    (hzS : z ∉ S) (hzP : z ∉ P) (hzQ : z ∉ Q)
    (haS : a ∉ S) (haQ : a ∉ Q) (haz : a ≠ z)
    (hbS : b ∉ S) (hbP : b ∉ P) (hbz : b ≠ z)
    (hpa : ¬ G.Adj p a) (hpaNe : p ≠ a) (hpb : G.Adj p b)
    (hqb : ¬ G.Adj q b) (hqbNe : q ≠ b) (hqa : G.Adj q a)
    (hpS : p ∉ S) (hqS : q ∉ S) (hqP : q ∉ P) (hpQ : p ∉ Q)
    (hpz : G.dist p z = 2) (hqz : G.dist q z = 2)
    (anchor : ∀ c ∈ S, G.Adj a c ∧ G.Adj b c ∧ G.dist c z = 2)
    (nonadj : ∀ c ∈ S, ∀ r ∈ P ∪ Q, ¬ G.Adj c r)
    (hPdeg : ∀ r ∈ P, s ≤ G.degree r)
    (hQdeg : ∀ r ∈ Q, s ≤ G.degree r)
    (hPN : ∀ r ∈ P, G.neighborFinset r ⊆ insert p (P ∪ Q ∪ T))
    (hQN : ∀ r ∈ Q, G.neighborFinset r ⊆ insert q (Q ∪ P ∪ T))
    (hPm : ∀ r ∈ P, G.Adj p r ∧ ¬ G.Adj q r)
    (hQm : ∀ r ∈ Q, G.Adj q r ∧ ¬ G.Adj p r) : False := by
  have hP2 (r : V) (hr : r ∈ P) : G.dist q r = 2 := by
    obtain ⟨x,hx,hrx⟩ := exclusive_cross_edge s hs P Q T hP hT hr (hPdeg r hr) (hPN r hr)
    exact two_edges (hQm x hx).1 hrx.symm (fun e => hqP (e.symm ▸ hr)) (hPm r hr).2
  have hQ2 (r : V) (hr : r ∈ Q) : G.dist p r = 2 := by
    obtain ⟨x,hx,hrx⟩ := exclusive_cross_edge s hs Q P T hQ hT hr (hQdeg r hr) (hQN r hr)
    exact two_edges (hPm x hx).1 hrx.symm (fun e => hpQ (e.symm ▸ hr)) (hQm r hr).2
  obtain ⟨c,hc⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hcp := (sees_shared_part s hs hCap S Q hS hQ hSQ hzS hzQ haS haQ haz
    hpa hpaNe hpb hpS (fun x hx => ⟨(anchor x hx).1,(anchor x hx).2.1⟩) hpz hQ2 c hc).symm
  have hcq := (sees_shared_part s hs hCap S P hS hP hSP hzS hzP hbS hbP hbz
    hqb hqbNe hqa hqS (fun x hx => ⟨(anchor x hx).2.1,(anchor x hx).1⟩) hqz hP2 c hc).symm
  have hcP : c ∉ P := fun h => Finset.disjoint_left.mp hSP hc h
  have hcQ : c ∉ Q := fun h => Finset.disjoint_left.mp hSQ hc h
  exact shared_excessive s hs hCap P Q hP hQ hPQ hzP hzQ hcP hcQ hcp hcq
    (anchor c hc).2.2
    (fun r hr => ⟨(hPm r hr).1,nonadj c hc r (Finset.mem_union_left _ hr)⟩)
    (fun r hr => ⟨(hQm r hr).1,nonadj c hc r (Finset.mem_union_right _ hr)⟩)


/-- If there are two missed middle-layer vertices and the remote classes
are disjoint, a full smaller class and the shared middle layer exceed the
distance-two budget at the middle-layer vertex of the larger class. -/
theorem disjoint_two_misses_impossible (s : ℕ) (hs : 4 ≤ s)
    (hCap : ∀ u : V, (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s)
    (S P Q : Finset V) (hS : S.card = s - 2)
    (hP : P.card = s - 2) (hQ : Q.card = s - 1)
    (hSP : Disjoint S P) (hSQ : Disjoint S Q) (hPQ : Disjoint P Q)
    (z a b p q : V)
    (hzS : z ∉ S) (hzP : z ∉ P) (hzQ : z ∉ Q)
    (hpS : p ∉ S) (hqS : q ∉ S) (hpQ : p ∉ Q) (hqP : q ∉ P) (hzp : z ≠ p)
    (hpb : G.Adj p b) (hqa : G.Adj q a) (hqz : G.dist q z = 2)
    (anchor : ∀ c ∈ S, G.Adj a c ∧ G.Adj b c ∧ G.dist c z = 2)
    (nonadj : ∀ c ∈ S, ∀ r ∈ P ∪ Q, ¬ G.Adj c r)
    (hPdeg : ∀ r ∈ P, s ≤ G.degree r)
    (hPN : ∀ r ∈ P, G.neighborFinset r ⊆ insert p (P ∪ Q))
    (hPm : ∀ r ∈ P, G.Adj p r ∧ ¬ G.Adj q r)
    (hQm : ∀ r ∈ Q, G.Adj q r) : False := by
  have noQ (c : V) (hc : c ∈ S) : ¬ G.Adj c q := by
    intro hcq
    have qc (r : V) (hr : r ∈ Q) : G.dist c r = 2 :=
      two_edges hcq (hQm r hr) (fun e => Finset.disjoint_left.mp hSQ (e ▸ hc) hr)
        (nonadj c hc r (Finset.mem_union_right _ hr))
    by_cases hcp : G.Adj c p
    · have hzU : z ∉ P ∪ Q := fun he => (Finset.mem_union.mp he).elim hzP hzQ
      have hsub : insert z (P ∪ Q) ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        rcases Finset.mem_insert.mp hx with e | hmem
        · exact e.symm ▸ (anchor c hc).2.2
        · rcases Finset.mem_union.mp hmem with hp | hq
          · exact two_edges hcp (hPm x hp).1 (fun e => Finset.disjoint_left.mp hSP (e ▸ hc) hp)
              (nonadj c hc x (Finset.mem_union_left _ hp))
          · exact qc x hq
      have hle := (Finset.card_le_card hsub).trans (hCap c)
      rw [Finset.card_insert_of_notMem hzU,Finset.card_union_of_disjoint hPQ,hP,hQ] at hle
      omega
    · have hp2 : G.dist c p = 2 :=
        two_edges (anchor c hc).2.1.symm hpb.symm (fun e => hpS (e ▸ hc)) hcp
      have hzU : z ∉ insert p Q := fun he => (Finset.mem_insert.mp he).elim hzp hzQ
      have hsub : insert z (insert p Q) ⊆ Finset.univ.filter (fun x => G.dist c x = 2) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        rcases Finset.mem_insert.mp hx with e | hmem
        · exact e.symm ▸ (anchor c hc).2.2
        · rcases Finset.mem_insert.mp hmem with e | hr
          · exact e.symm ▸ hp2
          · exact qc x hr
      have hle := (Finset.card_le_card hsub).trans (hCap c)
      rw [Finset.card_insert_of_notMem hzU,Finset.card_insert_of_notMem hpQ,hQ] at hle
      omega
  have hc2 (c : V) (hc : c ∈ S) : G.dist q c = 2 :=
    two_edges hqa (anchor c hc).1 (fun e => hqS (e.symm ▸ hc)) (fun h => noQ c hc h.symm)
  have hr2 (r : V) (hr : r ∈ P) : G.dist q r = 2 := by
    have hN : G.neighborFinset r ⊆ insert p (P ∪ Q ∪ (∅ : Finset V)) := by
      simpa using hPN r hr
    obtain ⟨x,hx,hrx⟩ := exclusive_cross_edge s hs P Q ∅ hP (by simp) hr (hPdeg r hr) hN
    exact two_edges (hQm x hx) hrx.symm (fun e => hqP (e.symm ▸ hr)) (hPm r hr).2
  have hzU : z ∉ S ∪ P := fun he => (Finset.mem_union.mp he).elim hzS hzP
  have hsub : insert z (S ∪ P) ⊆ Finset.univ.filter (fun x => G.dist q x = 2) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_insert.mp hx with e | hmem
    · exact e.symm ▸ hqz
    · rcases Finset.mem_union.mp hmem with hm | hm
      · exact hc2 x hm
      · exact hr2 x hm
  have hle := (Finset.card_le_card hsub).trans (hCap q)
  rw [Finset.card_insert_of_notMem hzU,Finset.card_union_of_disjoint hSP,hS,hP] at hle
  omega


omit [DecidableRel G.Adj] in
/-- The third near-saturation case, where one anchor misses two middle-layer
vertices and the other misses one. -/
theorem disjoint_three_misses_impossible (s : ℕ) (hs : 4 ≤ s)
    (hCap : ∀ u : V, (Finset.univ.filter (fun x => G.dist u x = 2)).card ≤ s)
    (P Q : Finset V) (hP : P.card = s - 2) (hQ : Q.card = s - 1)
    (hPQ : Disjoint P Q) (z c a b p q₁ q₂ : V)
    (hzP : z ∉ P) (hzQ : z ∉ Q)
    (hpQ : p ∉ Q) (hq₁P : q₁ ∉ P) (hq₂P : q₂ ∉ P)
    (hq₁Q : q₁ ∉ Q) (hq₂Q : q₂ ∉ Q)
    (hcP : c ∉ P) (hcQ : c ∉ Q)
    (hpz : p ≠ z) (hq₁z : q₁ ≠ z) (hq₂z : q₂ ≠ z)
    (hcpNe : c ≠ p) (hcq₁Ne : c ≠ q₁) (hcq₂Ne : c ≠ q₂)
    (hcz : G.dist c z = 2) (hq₁z₂ : G.dist q₁ z = 2) (hq₂z₂ : G.dist q₂ z = 2)
    (hca : G.Adj c a) (hcb : G.Adj c b) (hpb : G.Adj p b)
    (hq₁a : G.Adj q₁ a) (hq₂a : G.Adj q₂ a)
    (hcN : ∀ r ∈ P ∪ Q, ¬ G.Adj c r)
    (hpP : ∀ r ∈ P, G.Adj p r)
    (hQtouch : ∀ r ∈ Q, G.Adj q₁ r ∨ G.Adj q₂ r)
    (hq₁NoP : ∀ r ∈ P, ¬ G.Adj q₁ r)
    (hq₂NoP : ∀ r ∈ P, ¬ G.Adj q₂ r)
    (hcPOrQ₁ : G.Adj c p ∨ G.Adj c q₁)
    (hcPOrQ₂ : G.Adj c p ∨ G.Adj c q₂)
    (hcQ₁OrQ₂ : G.Adj c q₁ ∨ G.Adj c q₂)
    (q₁full : (∀ r ∈ Q, ¬ G.Adj q₁ r) → G.Adj q₁ p ∧ G.Adj q₁ q₂)
    (q₂full : (∀ r ∈ Q, ¬ G.Adj q₂ r) → G.Adj q₂ p ∧ G.Adj q₂ q₁) : False := by
  have unionBudget (v : V) (hvz : G.dist v z = 2)
      (hvP : ∀ r ∈ P, G.dist v r = 2) (hvQ : ∀ r ∈ Q, G.dist v r = 2) : False := by
    have hsub : insert z (P ∪ Q) ⊆ Finset.univ.filter (fun r => G.dist v r = 2) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_insert.mp hx with e | hm
      · exact e.symm ▸ hvz
      · exact (Finset.mem_union.mp hm).elim (hvP _) (hvQ _)
    have hzU : z ∉ P ∪ Q := fun h => (Finset.mem_union.mp h).elim hzP hzQ
    have hle := (Finset.card_le_card hsub).trans (hCap v)
    rw [Finset.card_insert_of_notMem hzU,Finset.card_union_of_disjoint hPQ,hP,hQ] at hle
    omega
  have middleDist {v r : V} (hcv : G.Adj c v) (hvr : G.Adj v r) (hr : r ∈ Q) : G.dist c r = 2 :=
    two_edges hcv hvr (fun e => hcQ (e.symm ▸ hr)) (hcN r (Finset.mem_union_right _ hr))
  have cPDist (hcp : G.Adj c p) (r : V) (hr : r ∈ P) : G.dist c r = 2 :=
    two_edges hcp (hpP r hr) (fun e => hcP (e.symm ▸ hr)) (hcN r (Finset.mem_union_left _ hr))
  have cQDist (hc₁ : G.Adj c q₁) (hc₂ : G.Adj c q₂) (r : V) (hr : r ∈ Q) : G.dist c r = 2 :=
    (hQtouch r hr).elim (fun he => middleDist hc₁ he hr) (fun he => middleDist hc₂ he hr)
  have hcp : G.Adj c p := by
    by_contra hn
    have cQ := cQDist (hcPOrQ₁.resolve_left hn) (hcPOrQ₂.resolve_left hn)
    have cp : G.dist c p = 2 := two_edges hcb hpb.symm hcpNe hn
    have hsub : insert p (insert z Q) ⊆ Finset.univ.filter (fun r => G.dist c r = 2) := by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_insert.mp hx with e | hm
      · exact e.symm ▸ cp
      · rcases Finset.mem_insert.mp hm with e | hr
        · exact e.symm ▸ hcz
        · exact cQ x hr
    have hpU : p ∉ insert z Q := fun he => (Finset.mem_insert.mp he).elim hpz hpQ
    have hle := (Finset.card_le_card hsub).trans (hCap c)
    rw [Finset.card_insert_of_notMem hpU,Finset.card_insert_of_notMem hzQ,hQ] at hle
    omega
  have impossible (v w : V) (hcv : G.Adj c v) (hcw : ¬ G.Adj c w) (hcwNe : c ≠ w)
      (hwa : G.Adj w a) (hwz : w ≠ z) (hwP : w ∉ P) (hwQ : w ∉ Q)
      (hvz₂ : G.dist v z = 2) (hvP : v ∉ P) (hvQ : v ∉ Q)
      (hN : ∀ r ∈ P, ¬ G.Adj v r) (hvW : ∀ r ∈ Q, G.Adj v r ∨ G.Adj w r)
      (hvFull : (∀ r ∈ Q, ¬ G.Adj v r) → G.Adj v p ∧ G.Adj v w) : False := by
    have wc : G.dist c w = 2 := two_edges hca hwa.symm hcwNe hcw
    have noQ (r : V) (hr : r ∈ Q) : ¬ G.Adj v r := by
      intro he
      have hcr := middleDist hcv he hr
      have hsub : insert r (insert w (insert z P)) ⊆
          Finset.univ.filter (fun x => G.dist c x = 2) := by
        intro x hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
        rcases Finset.mem_insert.mp hx with e | hm
        · exact e.symm ▸ hcr
        · rcases Finset.mem_insert.mp hm with e | hm
          · exact e.symm ▸ wc
          · rcases Finset.mem_insert.mp hm with e | hp
            · exact e.symm ▸ hcz
            · exact cPDist hcp x hp
      have hwU : w ∉ insert z P := fun he => (Finset.mem_insert.mp he).elim hwz hwP
      have hrU : r ∉ insert w (insert z P) := by
        intro hh
        rcases Finset.mem_insert.mp hh with e | hm
        · exact hwQ (e ▸ hr)
        · rcases Finset.mem_insert.mp hm with e | hm
          · exact hzQ (e ▸ hr)
          · exact Finset.disjoint_left.mp hPQ hm hr
      have hle := (Finset.card_le_card hsub).trans (hCap c)
      rw [Finset.card_insert_of_notMem hrU,Finset.card_insert_of_notMem hwU,
        Finset.card_insert_of_notMem hzP,hP] at hle
      omega
    obtain ⟨hvp,hvw⟩ := hvFull noQ
    apply unionBudget v hvz₂
    · intro r hr
      exact two_edges hvp (hpP r hr) (fun e => hvP (e.symm ▸ hr)) (hN r hr)
    · intro r hr
      exact two_edges hvw ((hvW r hr).resolve_left (noQ r hr))
        (fun e => hvQ (e.symm ▸ hr)) (noQ r hr)
  rcases hcQ₁OrQ₂ with hc₁ | hc₂
  · have hn₂ : ¬ G.Adj c q₂ := fun hc₂ => unionBudget c hcz (cPDist hcp) (cQDist hc₁ hc₂)
    exact impossible q₁ q₂ hc₁ hn₂ hcq₂Ne hq₂a hq₂z hq₂P hq₂Q hq₁z₂ hq₁P hq₁Q hq₁NoP
      hQtouch q₁full
  · have hn₁ : ¬ G.Adj c q₁ := fun hc₁ => unionBudget c hcz (cPDist hcp) (cQDist hc₁ hc₂)
    exact impossible q₂ q₁ hc₂ hn₁ hcq₁Ne hq₁a hq₁z hq₁P hq₁Q hq₂z₂ hq₂P hq₂Q hq₂NoP
      (fun r hr => (hQtouch r hr).symm) q₂full


omit [Fintype V] in
/-- Cardinal arithmetic reduces the top-order case to the three checked
geometric contradictions, up to exchanging the two anchors. -/
theorem near_partition_counts (s m₁ m₂ : ℕ) (hs : 4 ≤ s) (A B : Finset V)
    (hU : (A ∪ B).card = 2 * s - 3) (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂)
    (hA : A.card + m₁ ≤ s) (hB : B.card + m₂ ≤ s) :
    (m₁ = 1 ∧ m₂ = 1 ∧ A.card = s - 1 ∧ B.card = s - 1 ∧ (A ∩ B).card = 1) ∨
    (m₁ = 1 ∧ m₂ = 1 ∧
      ((A.card = s - 1 ∧ B.card = s - 2) ∨ (B.card = s - 1 ∧ A.card = s - 2)) ∧
      Disjoint A B) ∨
    (((m₁ = 1 ∧ m₂ = 2 ∧ A.card = s - 1 ∧ B.card = s - 2) ∨
      (m₁ = 2 ∧ m₂ = 1 ∧ A.card = s - 2 ∧ B.card = s - 1)) ∧ Disjoint A B) := by
  have he := Finset.card_union_add_card_inter A B
  rw [hU] at he
  by_cases hi : (A ∩ B).card = 0
  · have hd : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hi)
    by_cases h : m₁ + m₂ = 2
    · exact Or.inr (Or.inl ⟨by omega, by omega, by omega, hd⟩)
    · exact Or.inr (Or.inr ⟨by omega, hd⟩)
  · exact Or.inl ⟨by omega, by omega, by omega, by omega, by omega⟩

#print axioms overlap_impossible
#print axioms disjoint_two_misses_impossible
#print axioms disjoint_three_misses_impossible
#print axioms near_partition_counts
end Graph189DegreeTwoNearSaturation
