import Graph189BipartiteSmall

/-! The bipartite case of Ermelinda DeLaViña's Written on the Wall II
Graph Conjecture 189, with its original degree and vertex-distance hypothesis. -/
namespace Graph189Bipartite
open SimpleGraph
variable {V : Type*} [Fintype V] [Nontrivial V] [DecidableEq V]

theorem hamiltonian_bipartite (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.Connected) (hB : G.IsBipartite)
    (hσ : (Finset.univ.image (distEven G)).max' (by simp) ≤ 1 + secondSmallestDegree G) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  by_cases hcard : 7 ≤ Fintype.card V
  · exact hamiltonian_bipartite_of_card_ge_seven h hB hcard hσ
  obtain ⟨C⟩ := hB
  have h0 := part_nonempty h C 0
  have h1 := part_nonempty h C 1
  rcases lt_trichotomy (part C 0).card (part C 1).card with hlt | heq | hgt
  · exact hamiltonian_unbalanced h C hσ (by decide) h0 hlt
  · have hcs := part_card_sum C
    have hpos := Finset.card_pos.mpr h0
    have hcases : (part C 0).card = 1 ∨ (part C 0).card = 2 ∨ (part C 0).card = 3 := by omega
    rcases hcases with hcase | hcase | hcase
    · exact hamiltonian_card_two h (by omega)
    · exact hamiltonian_balanced_two h C hcase (heq ▸ hcase)
    · exact hamiltonian_balanced_three h C hσ hcase (heq ▸ hcase)
  · exact hamiltonian_unbalanced h C hσ (by decide) h1 hgt

#print axioms hamiltonian_bipartite
end Graph189Bipartite
