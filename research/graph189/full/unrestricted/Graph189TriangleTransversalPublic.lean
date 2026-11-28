module

public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite

public section

namespace Graph189TriangleTransversal

/-- Two large sets which each overlap a third with small union must overlap each other. -/
theorem overlap_of_union_caps {α : Type*} [DecidableEq α] (E F D : Finset α) {k t : ℕ}
    (hk : 3 * t + 3 ≤ k) (hE : k ≤ E.card + t) (hF : k ≤ F.card + t)
    (hD : k ≤ D.card + t) (hu : (F ∪ E).card ≤ k + 1)
    (hv : (F ∪ D).card ≤ k + 1) : (E ∩ D).Nonempty := by
  by_contra h
  have hcov : F ⊆ (F \ E) ∪ (F \ D) := by
    intro a ha
    by_cases he : a ∈ E
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨ha, fun hd => h ⟨a, Finset.mem_inter.mpr ⟨he, hd⟩⟩⟩
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, he⟩)
  have hc := Finset.card_le_card hcov
  have h₁ := Finset.card_union_le (F \ E) (F \ D)
  have h₂ := Finset.card_sdiff_add_card F E
  have h₃ := Finset.card_sdiff_add_card F D
  omega

open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbors that remain after deleting X. -/
def remainingNeighbors (X : Finset V) (v : V) : Finset V := G.neighborFinset v \ X

/-- Every triangle contains a vertex of X. -/
def MeetsEveryTriangle (X : Finset V) : Prop :=
  ∀ ⦃a b c : V⦄, a ∉ X → b ∉ X → c ∉ X → G.Adj a b → G.Adj b c → ¬G.Adj a c

private theorem remaining_large (X : Finset V) (b : V) {k : ℕ} (hb : k ≤ G.degree b) :
    k ≤ (remainingNeighbors G X b).card + X.card := by
  have h := Finset.card_le_card_sdiff_add_card (s := G.neighborFinset b) (t := X)
  simpa [remainingNeighbors] using le_trans (by simpa using hb : k ≤ (G.neighborFinset b).card) h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem two_edges {a b c : V} (hab : G.Adj a b) (hbc : G.Adj b c)
    (hne : a ≠ c) (hn : ¬G.Adj a c) : G.dist a c = 2 := by
  let p : G.Walk a c := .cons hab (.cons hbc .nil)
  have hp : G.dist a c ≤ 2 := by simpa [p] using G.dist_le p
  have hpos : 0 < G.dist a c := Nat.pos_of_ne_zero
    (fun h => hne (p.reachable.dist_eq_zero_iff.mp h))
  have hone : G.dist a c ≠ 1 := fun h => hn (dist_eq_one_iff_adj.mp h)
  omega

private theorem union_bound (X : Finset V) {k : ℕ} (ht : MeetsEveryTriangle G X)
    (cap : ∀ a, (Finset.univ.filter (fun u => G.dist a u = 2)).card ≤ k)
    {b c : V} (hb : b ∉ X) (hc : c ∉ X)
    (hm : (remainingNeighbors G X b ∩ remainingNeighbors G X c).Nonempty) :
    (remainingNeighbors G X b ∪ remainingNeighbors G X c).card ≤ k + 1 := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨hab, hac⟩ := Finset.mem_inter.mp ha
  have segment {v u : V} (hv : v ∉ X) (hav : a ∈ remainingNeighbors G X v)
      (huv : u ∈ remainingNeighbors G X v) (hne : u ≠ a) : G.dist a u = 2 := by
    obtain ⟨hav, haX⟩ := Finset.mem_sdiff.mp hav
    obtain ⟨huv, huX⟩ := Finset.mem_sdiff.mp huv
    have hav' := ((G.mem_neighborFinset v a).mp hav).symm
    have hvu := (G.mem_neighborFinset v u).mp huv
    exact two_edges G hav' hvu (Ne.symm hne) (ht haX hv huX hav' hvu)
  let S := Finset.univ.filter (fun u => G.dist a u = 2)
  have hsub : remainingNeighbors G X b ∪ remainingNeighbors G X c ⊆ insert a S := by
    intro u hu
    by_cases h : u = a
    · exact h ▸ Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases Finset.mem_union.mp hu with hu | hu
      · exact segment hb hab hu h
      · exact segment hc hac hu h
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le a S).trans
    (Nat.add_le_add_right (cap a) 1))

/-- In the triangle-free remainder, common-neighbor intersection is transitive on
vertices whose ambient degree is at least k, when k ≥ 3 |X| + 3. -/
theorem high_intersection_transitive (X : Finset V) {k : ℕ} (ht : MeetsEveryTriangle G X)
    (cap : ∀ a, (Finset.univ.filter (fun u => G.dist a u = 2)).card ≤ k)
    (hk : 3 * X.card + 3 ≤ k) {u v w : V} (hu : u ∉ X) (hv : v ∉ X) (hw : w ∉ X)
    (du : k ≤ G.degree u) (dv : k ≤ G.degree v) (dw : k ≤ G.degree w)
    (huv : (remainingNeighbors G X u ∩ remainingNeighbors G X v).Nonempty)
    (hvw : (remainingNeighbors G X v ∩ remainingNeighbors G X w).Nonempty) :
    (remainingNeighbors G X u ∩ remainingNeighbors G X w).Nonempty := by
  apply overlap_of_union_caps _ _ _ hk (remaining_large G X u du)
    (remaining_large G X v dv) (remaining_large G X w dw)
  · rw [Finset.union_comm]
    exact union_bound G X ht cap hu hv huv
  · exact union_bound G X ht cap hv hw hvw

/-- An even path in the triangle-free remainder whose even-indexed vertices are high
cannot close with a single edge. A simple odd cycle can place its sole low vertex,
if present, at index one by choosing its starting edge. -/
theorem no_closing_edge (X : Finset V) {k : ℕ} (ht : MeetsEveryTriangle G X)
    (cap : ∀ a, (Finset.univ.filter (fun u => G.dist a u = 2)).card ≤ k)
    (hk : 3 * X.card + 3 ≤ k) (f : ℕ → V) {m : ℕ} (hm : 0 < m)
    (outside : ∀ i ≤ 2 * m, f i ∉ X) (high : ∀ j ≤ m, k ≤ G.degree (f (2*j)))
    (edges : ∀ i < 2 * m, G.Adj (f i) (f (i+1))) : ¬G.Adj (f 0) (f (2*m)) := by
  let shared := fun u v => (remainingNeighbors G X u ∩ remainingNeighbors G X v).Nonempty
  have pair (j : ℕ) (hj : j < m) : shared (f (2*j)) (f (2*(j+1))) := by
    refine ⟨f (2*j+1), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_sdiff.mpr
      exact ⟨(G.mem_neighborFinset _ _).mpr (edges _ (by omega)), outside _ (by omega)⟩
    · apply Finset.mem_sdiff.mpr
      have he := edges (2*j+1) (by omega : 2*j+1 < 2*m)
      rw [show 2*j+1+1 = 2*(j+1) by omega] at he
      exact ⟨(G.mem_neighborFinset _ _).mpr he.symm, outside _ (by omega)⟩
  have chain (j : ℕ) (hj : j+1 ≤ m) : shared (f 0) (f (2*(j+1))) := by
    induction j with
    | zero => simpa using pair 0 hm
    | succ j ih =>
      apply high_intersection_transitive G X ht cap hk (outside 0 (by omega))
        (outside (2*(j+1)) (by omega)) (outside _ (by omega))
        (by simpa using high 0 (by omega)) (high _ (by omega)) (high _ (by omega))
      · exact ih (by omega)
      · exact pair (j+1) (by omega)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨a, ha⟩ := chain s (by omega)
  obtain ⟨hl, hr⟩ := Finset.mem_inter.mp ha
  obtain ⟨hl, haX⟩ := Finset.mem_sdiff.mp hl
  obtain ⟨hr, _⟩ := Finset.mem_sdiff.mp hr
  exact ht (outside 0 (by omega)) haX (outside _ (by omega))
    ((G.mem_neighborFinset _ _).mp hl) ((G.mem_neighborFinset _ _).mp hr).symm

end Graph189TriangleTransversal
