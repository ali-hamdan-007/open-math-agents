import Graph189DoubleDescent
import Graph189EdgeOrder

namespace Graph189CommonCutLabel
open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A high endpoint whose edge has no common neighbor outside the separator
touches every other label, once the order exceeds the edge bound at |S|-2. -/
theorem complete_label (hc : G.Connected) {S : Finset V} {i z : V} (hi : i ∈ S)
    (zi : G.Adj z i) (within : G.neighborFinset z ∩ G.neighborFinset i ⊆ S)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) (high : k ≤ G.degree i)
    (big : (S.card+1)*k+S.card < Fintype.card V) :
    ∀ j ∈ S, j ≠ i → G.Adj i j := by
  classical
  let C := G.neighborFinset z ∩ G.neighborFinset i
  have cut : C ⊆ S.erase i := by
    intro j hj
    have e := (G.mem_neighborFinset _ _).mp (mem_inter.mp hj).2
    exact mem_erase.mpr ⟨e.ne.symm,within hj⟩
  have order := Graph189EdgeOrder.edge_order hc zi cap
  change Fintype.card V ≤ 2*k+2+C.card+k*(k+1+C.card-G.degree i) at order
  have linear : Fintype.card V ≤ 2*k+2+C.card+k*(1+C.card) :=
    order.trans (Nat.add_le_add_left (Nat.mul_le_mul_left k (by omega)) _)
  have all : C = S.erase i := by
    apply Finset.eq_of_subset_of_card_le cut
    by_contra hlt
    have erased := card_erase_of_mem hi
    have c : C.card+2 ≤ S.card := by omega
    have prod := Nat.mul_le_mul_left k c
    nlinarith
  intro j hj ne
  have hj' : j ∈ C := all ▸ mem_erase.mpr ⟨ne,hj⟩
  exact (G.mem_neighborFinset _ _).mp (mem_inter.mp hj').2

/-- When the opposite side is large, a port touching any label must touch
every label adjacent to all the other labels. -/
theorem forced_contact (hc : G.Connected) {x i j : V} (S B : Finset V)
    (xs : x ∉ S) (xb : x ∉ B) (out : ∀ y, G.Adj x y → y ∉ B)
    (cut : ∀ b ∈ B, ∀ p : G.Walk x b, ∃ a ∈ S, a ∈ p.support)
    {k : ℕ} (cap : ∀ u, G.distEven u ≤ k+1) (big : S.card*k < B.card)
    (hi : i ∈ S) (hj : j ∈ S) (xj : G.Adj x j) (ij : G.Adj i j) :
    G.Adj x i := by
  by_contra missing
  have ne : x ≠ i := by rintro rfl; exact xs hi
  have lo := (hc x i).one_lt_dist_of_ne_of_not_adj ne missing
  have hi2 := hc.dist_triangle (u:=x) (v:=j) (w:=i)
  rw [dist_eq_one_iff_adj.mpr xj, dist_eq_one_iff_adj.mpr ij.symm] at hi2
  have dj : G.dist x j = G.dist j j + 1 := by simp [dist_eq_one_iff_adj.mpr xj]
  have di : G.dist x i = G.dist j i + 1 := by rw [dist_eq_one_iff_adj.mpr ij.symm]; omega
  exact ij.ne (Graph189DoubleDescent.unique_anchor hc x S B xs xb out cut k cap big xj hi hj di dj)

#print axioms complete_label
#print axioms forced_contact
end Graph189CommonCutLabel
