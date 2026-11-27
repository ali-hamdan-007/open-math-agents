import Mathlib.Combinatorics.SimpleGraph.Clique

namespace RadiusFourCharges

open SimpleGraph Finset

/-- In a graph of maximum degree at most one, an independent set can retain
every vertex except one endpoint of each edge. -/
theorem indepNum_add_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (h : ∀ {x y z : V}, G.Adj x y → G.Adj x z → y = z) :
    G.indepNum + Fintype.card G.edgeSet = Fintype.card V := by
  classical
  obtain ⟨s, hs⟩ := G.exists_isNIndepSet_indepNum
  have hn {x : V} (hx : x ∉ s) : ∃ y, y ∈ s ∧ G.Adj x y := by
    by_contra! hnone
    have hi : G.IsIndepSet ((insert x s : Finset V) : Set V) := by
      intro y hy z hz hne hadj
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hy hz
      rcases hy with rfl | hy
      · rcases hz with rfl | hz
        · exact hne rfl
        · exact hnone z hz hadj
      · rcases hz with rfl | hz
        · exact hnone y hy hadj.symm
        · exact hs.isIndepSet hy hz hne hadj
    have hc := hi.card_le_indepNum
    rw [Finset.card_insert_of_notMem hx, hs.card_eq] at hc
    omega
  choose neighbor hmem hadj using fun x : (sᶜ : Finset V) =>
    hn (Finset.mem_compl.mp x.property)
  let f (x : (sᶜ : Finset V)) : G.edgeSet := ⟨s(x.val, neighbor x), hadj x⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      have he' := Subtype.ext_iff.mp he
      change s(x.val, neighbor x) = s(y.val, neighbor y) at he'
      rcases Sym2.eq_iff.mp he' with he' | he'
      · exact Subtype.ext he'.1
      · exact False.elim ((Finset.mem_compl.mp x.property) (he'.1 ▸ hmem y))
    · rintro ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | hf v w =>
          change G.Adj v w at he
          by_cases hv : v ∈ s
          · have hw : w ∉ s := fun hw => hs.isIndepSet hv hw he.ne he
            let x : (sᶜ : Finset V) := ⟨w, Finset.mem_compl.mpr hw⟩
            have hnx : neighbor x = v := h (hadj x) he.symm
            refine ⟨x, Subtype.ext ?_⟩
            change s(w, neighbor x) = s(v, w)
            rw [hnx, Sym2.eq_swap]
          · let x : (sᶜ : Finset V) := ⟨v, Finset.mem_compl.mpr hv⟩
            have hnx : neighbor x = w := h (hadj x) he
            refine ⟨x, Subtype.ext ?_⟩
            change s(v, neighbor x) = s(v, w)
            rw [hnx]
  rw [← Fintype.card_congr (Equiv.ofBijective f hf), Fintype.card_coe,
    Finset.card_compl, ← hs.card_eq]
  have hcard := s.card_le_univ
  omega

/-- A four-cycle-free graph has a matching plus isolated vertices in
each open neighborhood. Its local independence number is its local degree
minus the number of edges of that matching. -/
theorem neighbor_indepNum_add_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ ∃ a b c d : V, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) (v : V) :
    (G.induce (G.neighborSet v)).indepNum +
      Fintype.card ((G.induce (G.neighborSet v)).edgeSet) = G.degree v := by
  rw [← G.card_neighborSet_eq_degree v]
  apply indepNum_add_edges
  intro x y z hxy hxz
  apply Subtype.ext
  by_contra hne
  have hyv : G.Adj v y.val := y.property
  have hxv : G.Adj v x.val := x.property
  have hzv : G.Adj v z.val := z.property
  have hyx : G.Adj x.val y.val := hxy
  have hzx : G.Adj x.val z.val := hxz
  exact h ⟨v, y.val, x.val, z.val, hyv.ne, hxv.ne, hzv.ne,
    hyx.ne.symm, hne, hzx.ne, hyv, hyx.symm, hzx, hzv.symm⟩

#print axioms indepNum_add_edges
#print axioms neighbor_indepNum_add_edges

end RadiusFourCharges
