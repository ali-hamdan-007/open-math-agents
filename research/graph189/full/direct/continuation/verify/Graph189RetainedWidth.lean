import Graph189WedgeOrder
import Mathlib.Tactic.Linarith

open SimpleGraph Finset

namespace Graph189RetainedWidth

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem union_lower {a b c : V} (hab : G.Adj b a) (hbc : G.Adj b c)
    (hne : a ≠ c) (hac : ¬G.Adj a c) :
    G.degree a + G.degree c + 2 ≤
      (G.neighborFinset b ∪ (G.neighborFinset a ∪ G.neighborFinset c)).card +
      (G.neighborFinset a ∩ G.neighborFinset c).card := by
  classical
  let S := G.neighborFinset a ∪ G.neighborFinset c
  have ha : a ∉ S := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact G.loopless.irrefl a ((G.mem_neighborFinset _ _).mp h)
    · exact hac ((G.mem_neighborFinset _ _).mp h).symm
  have hc : c ∉ S := by simp [S, G.mem_neighborFinset, hac]
  have ha' : a ∉ insert c S := by simp [hne, ha]
  have sub : insert a (insert c S) ⊆ G.neighborFinset b ∪ S := by
    intro u hu
    rcases mem_insert.mp hu with rfl|hu
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hab)
    rcases mem_insert.mp hu with rfl|hu
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hbc)
    · exact mem_union_right _ hu
  have h := card_le_card sub
  rw [card_insert_of_notMem ha', card_insert_of_notMem hc] at h
  have hh := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset c)
  rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree] at hh
  change S.card + _ = _ at hh
  change _ ≤ (G.neighborFinset b ∪ S).card + _
  omega

/-- Retains both endpoint degrees of an actual three-edge geodesic. -/
theorem geodesic_degree_width (hc : G.Connected) {x i j y : V}
    (hxi : G.Adj x i) (hij : G.Adj i j) (hjy : G.Adj j y) (hxy : G.dist x y = 3)
    {k : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) :
    2 * Fintype.card V + k*(G.degree x + G.degree y) ≤
      4*k + 2*k*k + (k+1)*((G.neighborFinset x ∩ G.neighborFinset j).card +
           (G.neighborFinset y ∩ G.neighborFinset i).card) := by
  have dx := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  have dy := hc.dist_triangle (u:=x) (v:=j) (w:=y)
  rw [hxy, dist_eq_one_iff_adj.mpr hxi] at dx
  rw [hxy, dist_eq_one_iff_adj.mpr hjy] at dy
  have nxj : ¬G.Adj x j := by
    intro hh
    rw [dist_eq_one_iff_adj.mpr hh] at dy
    omega
  have nyi : ¬G.Adj y i := by
    intro hh
    rw [dist_eq_one_iff_adj.mpr hh.symm] at dx
    omega
  have hxj : x ≠ j := by rintro rfl; simp at dy
  have hyi : y ≠ i := by rintro rfl; simp at dx
  have w₁ := Graph189WedgeOrder.wedge_order hc hxi.symm hij nxj cap
  have w₂ := Graph189WedgeOrder.wedge_order hc hjy hij.symm nyi cap
  have u₁ := Nat.mul_le_mul_left (k+1) (union_lower hxi.symm hij hxj nxj)
  have u₂ := Nat.mul_le_mul_left (k+1) (union_lower hjy hij.symm hyi nyi)
  have e₁ := Nat.mul_le_mul_left k (cap i)
  have e₂ := Nat.mul_le_mul_left k (cap j)
  nlinarith only [w₁,w₂,u₁,u₂,e₁,e₂]

#print axioms geodesic_degree_width
end Graph189RetainedWidth
