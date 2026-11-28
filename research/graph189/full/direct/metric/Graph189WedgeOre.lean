import Graph189WedgeParity

namespace Graph189WedgeParity
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Covering the center's second layer forces the neighborhood-union form of
the local Ore condition at any wedge in the large-order regime. -/
theorem ore_of_covered (hc : G.Connected) {u w v : V} (e : G.Adj u w)
    (f : G.Adj w v) {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1)
    (order : 3*k+2 < Fintype.card V)
    (covered : ∀ b, G.dist w b = 2 → G.Adj u b ∨ G.Adj v b) :
    (G.neighborFinset u ∪ G.neighborFinset v ∪ G.neighborFinset w).card ≤
      G.degree u + G.degree v := by
  let Nu := G.neighborFinset u
  let Nv := G.neighborFinset v
  let Nw := G.neighborFinset w
  let T := univ.filter fun t => 3 ≤ G.dist w t ∧ G.dist u t = G.dist w t ∧
    G.dist v t = G.dist w t ∧ ¬Even (G.dist w t)
  have no : T = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨h₁,h₂,h₃,_⟩ := (mem_filter.mp ht).2
    obtain ⟨b,dist,nu,nv⟩ := missed_of_remote hc h₂ h₃ h₁
    exact (covered b dist).elim nu nv
  have num := wedge_count hc e f cap
  change Fintype.card V + (Nw \ (Nu ∪ Nv)).card ≤
    3*(k+1) + ((Nu ∩ Nv) ∩ Nw).card + T.card at num
  rw [no,card_empty] at num
  have small := card_le_card (inter_subset_left (s₁ := Nu ∩ Nv) (s₂ := Nw))
  have uv := card_union_add_card_inter Nu Nv
  have up : Nu ∪ Nv ∪ Nw = (Nu ∪ Nv) ∪ (Nw \ (Nu ∪ Nv)) := by
    ext x
    simp only [mem_union,mem_sdiff]
    tauto
  have top := card_union_le (Nu ∪ Nv) (Nw \ (Nu ∪ Nv))
  change (Nu ∪ Nv ∪ Nw).card ≤ Nu.card + Nv.card
  rw [up]
  omega

/-- The classical ball bound on endpoint degrees may be relaxed by one unit
for the neighborhood-union L₁ conclusion under the full parity hypothesis. -/
theorem local_ore_one_of_ball (hc : G.Connected) {u w v : V} (e : G.Adj u w)
    (f : G.Adj w v) {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1)
    (order : 3*k+2 < Fintype.card V)
    (size : (univ.filter fun b => G.dist w b ≤ 2).card ≤ G.degree u + G.degree v + 2) :
    (G.neighborFinset u ∪ G.neighborFinset v ∪ G.neighborFinset w).card ≤
      G.degree u + G.degree v + 1 := by
  let N := G.neighborFinset u ∪ G.neighborFinset v ∪ G.neighborFinset w
  let B := univ.filter fun b => G.dist w b ≤ 2
  have sub : N ⊆ B := by
    intro b hb
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_union.mp hb with h | h
    · rcases mem_union.mp h with h | h
      · have hh := hc.dist_triangle (u := w) (v := u) (w := b)
        rw [dist_eq_one_iff_adj.mpr e.symm,
          dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h)] at hh
        exact hh
      · have hh := hc.dist_triangle (u := w) (v := v) (w := b)
        rw [dist_eq_one_iff_adj.mpr f,
          dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h)] at hh
        exact hh
    · rw [dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp h)]
      decide
  change N.card ≤ G.degree u + G.degree v + 1
  by_contra! h
  change B.card ≤ G.degree u + G.degree v + 2 at size
  have eq := eq_of_subset_of_card_le sub (by omega)
  have covered : ∀ b, G.dist w b = 2 → G.Adj u b ∨ G.Adj v b := by
    intro b hb
    have hmem : b ∈ B := mem_filter.mpr ⟨mem_univ _,by omega⟩
    rw [← eq] at hmem
    rcases mem_union.mp hmem with huv | hw
    · rcases mem_union.mp huv with hu | hv
      · exact Or.inl ((G.mem_neighborFinset _ _).mp hu)
      · exact Or.inr ((G.mem_neighborFinset _ _).mp hv)
    · have hone := dist_eq_one_iff_adj.mpr ((G.mem_neighborFinset _ _).mp hw)
      omega
  have core := ore_of_covered hc e f cap order covered
  change N.card ≤ G.degree u + G.degree v at core
  omega

/-- At large order the local balance of the central degree with the two
endpoint degrees suffices, including for irregular graphs. -/
theorem local_ore_one_of_degree (hc : G.Connected) {u w v : V} (e : G.Adj u w)
    (f : G.Adj w v) {k : ℕ} (cap : ∀ a, G.distEven a ≤ k+1)
    (order : 3*k+2 < Fintype.card V)
    (balance : G.degree w + k ≤ G.degree u + G.degree v + 1) :
    (G.neighborFinset u ∪ G.neighborFinset v ∪ G.neighborFinset w).card ≤
      G.degree u + G.degree v + 1 := by
  apply local_ore_one_of_ball hc e f cap order
  let E := univ.filter fun t => Even (G.dist w t)
  let B := univ.filter fun t => G.dist w t ≤ 2
  have inc : B ⊆ G.neighborFinset w ∪ E := by
    intro t ht
    have d := (mem_filter.mp ht).2
    by_cases one : G.dist w t = 1
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp one))
    · refine mem_union_right _ (mem_filter.mpr ⟨mem_univ _,?_⟩)
      rw [Nat.even_iff]
      omega
  have a := card_le_card inc
  have b := card_union_le (G.neighborFinset w) E
  have c : E.card ≤ k+1 := cap w
  have m : (G.neighborFinset w).card = G.degree w := G.card_neighborFinset_eq_degree w
  change B.card ≤ G.degree u + G.degree v + 2
  omega

#print axioms local_ore_one_of_degree

#print axioms ore_of_covered
#print axioms local_ore_one_of_ball
end Graph189WedgeParity
