module

public import Graph189CutCore

public section
namespace Graph189CutBounds
open SimpleGraph Finset Graph189CutCore
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The large-order regime excludes all leaves and isolated vertices. -/
theorem two_le_degree [DecidableRel G.Adj] [Nontrivial V] (hc : G.Connected)
    {k : ℕ} (hσ : ∀ v, evenCard G v ≤ 1+k) (horder : 2*k+3 ≤ Fintype.card V)
    (v : V) : 2 ≤ G.degree v := by
  classical
  obtain ⟨a,hva⟩ := hc.preconnected.exists_adj_of_nontrivial v
  have hp : 0 < (G.neighborFinset v).card := card_pos.mpr ⟨a,by simpa using hva⟩
  by_contra! hn
  rw [← card_neighborFinset_eq_degree] at hn
  obtain ⟨c,hN⟩ := card_eq_one.mp (show (G.neighborFinset v).card = 1 by omega)
  have hadj (u : V) : G.Adj v u ↔ u = c := by
    rw [← mem_neighborFinset, hN, mem_singleton]
  have hvc := (hadj c).mpr rfl
  have S : Side G c ({v} : Finset V) := by
    refine ⟨singleton_nonempty _,by simpa using hvc.ne.symm,?_⟩
    intro x y hx he _
    have hx' : x = v := mem_singleton.mp hx
    exact (hadj _).mp (hx' ▸ he)
  have hh := S.parity_bound hc hσ
  have hs := card_add_card_compl ({v} : Finset V)
  rw [card_singleton] at hs
  omega

/-- The other side's gate parity budget bounds the order of a remote side. -/
theorem side_card_le_two_k {k : ℕ} (hc : G.Connected)
    (hσ : ∀ v, evenCard G v ≤ 1+k) {c : V} {A B : Finset V}
    (hA : Side G c A) (hB : Side G c B) (hAB : Disjoint A B) : A.card ≤ 2*k := by
  have hs : insert c A ⊆ Bᶜ := by
    intro y hy
    apply mem_compl.mpr
    rcases mem_insert.mp hy with rfl | hy
    · exact hB.outside
    · exact Finset.disjoint_left.mp hAB hy
  have hh := card_le_card hs
  rw [card_insert_of_notMem hA.outside] at hh
  have := hB.parity_bound hc hσ
  omega

#print axioms two_le_degree
#print axioms side_card_le_two_k
end Graph189CutBounds
