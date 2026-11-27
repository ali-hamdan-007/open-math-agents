import Graph189DegreeTwoRooted

namespace Graph189EccFour
open SimpleGraph Graph189LowDegreeTwo Graph189DegreeTwoOuter
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For a degree-two root of eccentricity four, either the order is at most
twice the second degree plus three or the layout has the adjacent one-miss
anchors and a single far vertex. -/
theorem layout_of_order_large (z a b : V) (h : G.Connected)
    (hZ : G.neighborFinset z = {a,b}) (hab : a ≠ b)
    (hecc : ∀ x, G.dist z x ≤ 4) (hfar : ∃ f, G.dist z f = 4)
    (hs : 3 ≤ G.secondSmallestDegree)
    (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree)
    (horder : 2*G.secondSmallestDegree+3 < Fintype.card V) :
    let B := Finset.univ.filter (fun x => G.dist z x = 2)
    let C := Finset.univ.filter (fun x => G.dist z x = 3)
    let D := Finset.univ.filter (fun x => G.dist z x = 4)
    G.Adj a b ∧ B.card = G.secondSmallestDegree-1 ∧ D.card = 1 ∧
      B.card+C.card+D.card+3 = Fintype.card V ∧
      ∃ p ∈ B, ∃ q ∈ B, p ≠ q ∧
        (∀ x ∈ B, G.Adj a x ↔ x ≠ p) ∧ (∀ x ∈ B, G.Adj b x ↔ x ≠ q) := by
  classical
  let B := Finset.univ.filter (fun x => G.dist z x = 2)
  let C := Finset.univ.filter (fun x => G.dist z x = 3)
  let D := Finset.univ.filter (fun x => G.dist z x = 4)
  let s := G.secondSmallestDegree
  change G.Adj a b ∧ B.card = s-1 ∧ D.card = 1 ∧
      B.card+C.card+D.card+3 = Fintype.card V ∧ _
  have hza : G.Adj z a := (G.mem_neighborFinset z a).mp (by simp [hZ])
  have hzb : G.Adj z b := (G.mem_neighborFinset z b).mp (by simp [hZ])
  have hzd : G.degree z = 2 := by rw [← G.card_neighborFinset_eq_degree,hZ,Finset.card_pair hab]
  have mB (x : V) : x ∈ B ↔ G.dist z x = 2 := by simp [B]
  have mC (x : V) : x ∈ C ↔ G.dist z x = 3 := by simp [C]
  have mD (x : V) : x ∈ D ↔ G.dist z x = 4 := by simp [D]
  have all (x : V) : x = z ∨ x ∈ ({a,b} : Finset V) ∨ x ∈ B ∨ x ∈ C ∨ x ∈ D := by
    have hx : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 ∨
        G.dist z x = 3 ∨ G.dist z x = 4 := by have := hecc x; omega
    rcases hx with h0 | h1 | h2 | h3 | h4
    · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
    · exact Or.inr (Or.inl (hZ ▸ (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)))
    · exact Or.inr (Or.inr (Or.inl ((mB x).mpr h2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ((mC x).mpr h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ((mD x).mpr h4))))
  have hT (x : V) (hx : x ∈ ({a,b} : Finset V)) : G.dist z x = 1 :=
    dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset z x).mp (hZ.symm ▸ hx))
  have hdisB : Disjoint ({a,b} : Finset V) B := by
    exact Finset.disjoint_left.mpr (fun x hx hy => by have := hT x hx; have := (mB x).mp hy; omega)
  have hdisC : Disjoint (({a,b} : Finset V) ∪ B) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (mC x).mp hy
    rcases Finset.mem_union.mp hx with hz | hz
    · have := hT x hz; omega
    · have := (mB x).mp hz; omega
  have hdisD : Disjoint (({a,b} : Finset V) ∪ B ∪ C) D := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have := (mD x).mp hy
    rcases Finset.mem_union.mp hx with hz | hz
    · rcases Finset.mem_union.mp hz with ht | ht
      · have := hT x ht; omega
      · have := (mB x).mp ht; omega
    · have := (mC x).mp hz; omega
  have hun : insert z ((({a,b} : Finset V) ∪ B ∪ C) ∪ D) = Finset.univ := by
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_univ,iff_true]
    have ha := all x
    simp only [Finset.mem_insert] at ha
    tauto
  have hzEmpty : z ∉ ((({a,b} : Finset V) ∪ B ∪ C) ∪ D) := by
    simp [mB,mC,mD, G.ne_of_adj hza, G.ne_of_adj hzb]
  have hL := congrArg Finset.card hun
  rw [Finset.card_insert_of_notMem hzEmpty,Finset.card_union_of_disjoint hdisD,
    Finset.card_union_of_disjoint hdisC,Finset.card_union_of_disjoint hdisB,
    Finset.card_pair hab,Finset.card_univ] at hL
  have hBD : B.card+D.card ≤ s := by
    have hsub : insert z (B ∪ D) ⊆ Finset.univ.filter (fun x => Even (G.dist z x)) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp
      rcases Finset.mem_union.mp hx with hb | hd
      · simp [(mB x).mp hb]
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _,((mD x).mp hd).symm ▸ (by decide : Even (4 : ℕ))⟩
    have hC := (Finset.card_le_card hsub).trans (hσ z)
    have hdis : Disjoint B D := Finset.disjoint_left.mpr (fun x hx hy => by
      have := (mB x).mp hx; have := (mD x).mp hy; omega)
    rw [Finset.card_insert_of_notMem (by simp [mB,mD]),Finset.card_union_of_disjoint hdis] at hC
    omega
  have hDpos : 0 < D.card := by obtain ⟨f,hf⟩ := hfar; exact Finset.card_pos.mpr ⟨f,(mD f).mpr hf⟩
  have reachB (r : V) (hr : r ∈ C) : ∃ w ∈ B, G.Adj w r := by
    obtain ⟨w,hw,hadj⟩ := split_three h ((mC r).mp hr)
    exact ⟨w,(mB w).mpr hw,hadj⟩
  have miss (u : V) (hu : G.Adj z u) : ∃ w ∈ B, ¬ G.Adj u w := by
    by_contra! hm
    have hsub : C ⊆ Finset.univ.filter (fun x => G.dist u x = 2) := by
      intro x hx
      obtain ⟨w,hw,hadj⟩ := reachB x hx
      have hzU := dist_eq_one_iff_adj.mpr hu
      have hzX := (mC x).mp hx
      have hne : u ≠ x := by intro eq; rw [eq,hzX] at hzU; contradiction
      have hn : ¬ G.Adj u x := by
        intro hux
        have hb := h.dist_triangle (u := z) (v := u) (w := x)
        rw [hzU,hzX,dist_eq_one_iff_adj.mpr hux] at hb
        omega
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,two_edges (hm w hw) hadj hne hn⟩
    have hc := (Finset.card_le_card hsub).trans (distance_two_cap s hσ u)
    omega
  have count (u v : V) (hu : G.Adj z u) (huv : u ≠ v) (hpair : G.neighborFinset z = {u,v}) :
      G.Adj u v ∧ B.card = s-1 ∧ D.card = 1 ∧
        ∃ p ∈ B, ∀ x ∈ B, G.Adj u x ↔ x ≠ p := by
    obtain ⟨p,hp,hnp⟩ := miss u hu
    have hud := (Graph189Bipartite.degree_pair u z (G.ne_of_adj hu.symm)).resolve_right (by
      rw [hzd]
      omega)
    let N := B.filter (G.Adj u)
    have hNpc : N.card + 1 ≤ B.card := by
      have hsub : N ⊆ B.erase p := by
        intro x hx
        have ⟨hxB,hux⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_erase.mpr ⟨fun eq => hnp (eq ▸ hux),hxB⟩
      have h := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hp] at h
      have hpos := Finset.card_pos.mpr (show B.Nonempty from ⟨p,hp⟩)
      omega
    have hun : ∀ x ∈ G.neighborFinset u, x = z ∨ x = v ∨ x ∈ N := by
      intro x hx
      have hux := (G.mem_neighborFinset u x).mp hx
      have ht := h.dist_triangle (u := z) (v := u) (w := x)
      rw [dist_eq_one_iff_adj.mpr hu,dist_eq_one_iff_adj.mpr hux] at ht
      have hz : G.dist z x = 0 ∨ G.dist z x = 1 ∨ G.dist z x = 2 := by omega
      rcases hz with h0 | h1 | h2
      · exact Or.inl ((h.preconnected z x).dist_eq_zero_iff.mp h0).symm
      · have hzv : x = u ∨ x = v := by
          have hz := (G.mem_neighborFinset z x).mpr (dist_eq_one_iff_adj.mp h1)
          simpa [hpair] using hz
        exact Or.inr (Or.inl (hzv.resolve_left (G.ne_of_adj hux).symm))
      · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨(mB x).mpr h2,hux⟩))
    have hcard : G.degree u ≤ N.card + 2 := by
      rw [← G.card_neighborFinset_eq_degree]
      have he := Finset.card_le_card (show G.neighborFinset u ⊆ insert z (insert v N) from
        fun x hx => by simpa using hun x hx)
      have h₁ := Finset.card_insert_le z (insert v N)
      have h₂ := Finset.card_insert_le v N
      omega
    have hab : G.Adj u v := by
      by_contra hn
      have he := Finset.card_le_card (show G.neighborFinset u ⊆ insert z N from by
        intro x hx
        rcases hun x hx with rfl | heq | hx'
        · simp
        · exact (hn (heq ▸ (G.mem_neighborFinset u x).mp hx)).elim
        · exact Finset.mem_insert_of_mem hx')
      rw [G.card_neighborFinset_eq_degree] at he
      have h₁ := Finset.card_insert_le z N
      omega
    refine ⟨hab,by omega,by omega,p,hp,fun x hx => ⟨?_,?_⟩⟩
    · intro had eq
      exact hnp (eq ▸ had)
    · intro hxp
      by_contra hnx
      have hsub : N ⊆ (B.erase p).erase x := by
        intro y hy
        obtain ⟨hyB,hay⟩ := Finset.mem_filter.mp hy
        exact Finset.mem_erase.mpr ⟨fun eq => hnx (eq ▸ hay),
          Finset.mem_erase.mpr ⟨fun eq => hnp (eq ▸ hay),hyB⟩⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxp,hx⟩),Finset.card_erase_of_mem hp] at hle
      omega
  obtain ⟨hab',hBcard,hDcard,p,hp,hpa⟩ := count a b hza hab hZ
  obtain ⟨_,_,_,q,hq,hqb⟩ := count b a hzb hab.symm (by simpa [Finset.pair_comm] using hZ)
  refine ⟨hab',hBcard,hDcard,by omega,p,hp,q,hq,?_,hpa,hqb⟩
  intro eq
  obtain ⟨w,hzw,hwp⟩ := split_two h ((mB p).mp hp)
  have hw : w ∈ ({a,b} : Finset V) := hZ ▸ (G.mem_neighborFinset z w).mpr hzw
  rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
  · exact (hpa p hp).1 hwp rfl
  · exact (hqb p hp).1 hwp eq

#print axioms layout_of_order_large
end Graph189EccFour
