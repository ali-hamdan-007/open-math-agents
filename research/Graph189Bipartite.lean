import Graph189BipartiteUnbalanced
import Graph189BipartiteBalanced

namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
theorem part_nonempty (h : G.Connected) (C : G.Coloring (Fin 2)) (c : Fin 2) :
    (part C c).Nonempty := by
  obtain ⟨x⟩ := h.nonempty
  obtain ⟨y,hxy⟩ := h.preconnected.exists_adj_of_nontrivial x
  have hne := C.valid hxy
  have hc : C x = c ∨ C y = c := by
    generalize C x = a at hne ⊢
    generalize C y = b at hne ⊢
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
  exact hc.elim (fun hx => ⟨x,(mem_part C c x).mpr hx⟩)
    (fun hy => ⟨y,(mem_part C c y).mpr hy⟩)

omit [Nontrivial V] in
theorem part_card_sum (C : G.Coloring (Fin 2)) :
    (part C 0).card + (part C 1).card = Fintype.card V := by
  have hd : Disjoint (part C 0) (part C 1) := by
    refine Finset.disjoint_left.mpr ?_
    intro v h₀ h₁
    rw [mem_part] at h₀ h₁
    have : (0 : Fin 2) = 1 := h₀.symm.trans h₁
    exact (by decide : (0 : Fin 2) ≠ 1) this
  have hu : part C 0 ∪ part C 1 = Finset.univ := by
    ext v
    simp only [Finset.mem_union, mem_part, Finset.mem_univ, iff_true]
    generalize C v = q
    fin_cases q <;> simp
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

/-- DeLaViña's conjecture 189 for bipartite graphs of order at least seven.
For smaller order, the same argument handles every unbalanced bipartition. -/
theorem hamiltonian_bipartite_of_card_ge_seven [DecidableRel G.Adj]
    (h : G.Connected) (hB : G.IsBipartite) (hcard : 7 ≤ Fintype.card V)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨C⟩ := hB
  rcases lt_trichotomy (part C 0).card (part C 1).card with hlt | heq | hgt
  · exact hamiltonian_unbalanced h C hσ (by decide) (part_nonempty h C 0) hlt
  · have hlarge : 4 ≤ (part C 0).card := by have := part_card_sum C; omega
    obtain ⟨z,hdeg⟩ : ∃ z : V, ∀ x, x ≠ z → secondSmallestDegree G ≤ G.degree x := by
      by_cases hlow : ∃ y, G.degree y < secondSmallestDegree G
      · obtain ⟨y,hy⟩ := hlow
        exact ⟨y,fun x hx => (degree_pair x y hx).resolve_right (by omega)⟩
      · obtain ⟨y⟩ := h.nonempty
        exact ⟨y,fun x _ => by by_contra! hx; exact hlow ⟨x,hx⟩⟩
    have hz : z ∈ part C 0 ∨ z ∈ part C 1 := by
      simp only [mem_part]
      generalize C z = q
      fin_cases q <;> simp
    rcases hz with hz | hz
    · exact hamiltonian_balanced_large h C hσ (by decide) heq hlarge z hz hdeg
    · exact hamiltonian_balanced_large h C hσ (by decide) heq.symm (heq ▸ hlarge) z hz hdeg
  · exact hamiltonian_unbalanced h C hσ (by decide) (part_nonempty h C 1) hgt

#print axioms hamiltonian_bipartite_of_card_ge_seven
end Graph189Bipartite
