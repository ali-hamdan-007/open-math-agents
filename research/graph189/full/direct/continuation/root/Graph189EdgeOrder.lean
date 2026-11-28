import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.VertexDistance
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graph189EdgeOrder
open Finset SimpleGraph
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem predecessor {x z : V} {j : ℕ} (hz : G.dist x z = j+1) :
    ∃ a, G.dist x a = j ∧ G.Adj a z := by
  have hr : G.dist z x = j+1 := by rwa [dist_comm]
  have hp : G.Reachable z x := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hp.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at hz
  | cons he tail =>
    rename_i a
    have ht : tail.length = j := by rw [Walk.length_cons,hr] at hlen; omega
    have hh : G.dist x a ≤ j := by rw [dist_comm]; exact ht ▸ G.dist_le tail
    have := he.diff_dist_adj (u := x)
    exact ⟨a,by omega,he.symm⟩

/-- The order bound uses one oriented edge. Use the orientation with larger
second endpoint degree for the strongest estimate. -/
theorem edge_order (hc : G.Connected) {x y : V} (hxy : G.Adj x y) {k : ℕ}
    (cap : ∀ v, G.distEven v ≤ k+1) :
    Fintype.card V ≤ 2*k+2+(G.neighborFinset x ∩ G.neighborFinset y).card +
      k*(k+1+(G.neighborFinset x ∩ G.neighborFinset y).card-G.degree y) := by
  classical
  let E (v : V) := Finset.univ.filter (fun w => Even (G.dist v w))
  let X := G.neighborFinset x
  let Y := G.neighborFinset y
  let C := X ∩ Y
  let A := E x \ Y
  let T := univ.filter (fun w => 3 ≤ G.dist x w ∧ 3 ≤ G.dist y w ∧ ¬Even (G.dist x w))
  have ecap (v : V) : (E v).card ≤ k+1 := cap v
  have yw (w : V) (hw : w ∈ Y) : G.Adj y w := (G.mem_neighborFinset _ _).mp hw
  have yn (w : V) (hw : w ∈ Y \ X) : w ∈ E x := by
    obtain ⟨hy,hn⟩ := mem_sdiff.mp hw
    have htwo := hc.dist_triangle (u := x) (v := y) (w := w)
    rw [dist_eq_one_iff_adj.mpr hxy,dist_eq_one_iff_adj.mpr (yw _ hy)] at htwo
    have notone : G.dist x w ≠ 1 := fun h => hn ((G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp h))
    exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
  have asub : A ∪ (Y \ X) ⊆ E x := by
    intro w hw
    exact (mem_union.mp hw).elim (fun ha => (mem_sdiff.mp ha).1) (yn w)
  have dj : Disjoint A (Y \ X) := by
    rw [Finset.disjoint_left]
    exact fun _ ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1
  have ac : A.card ≤ k+1+C.card-G.degree y := by
    have hh := (card_le_card asub).trans (ecap x)
    rw [card_union_of_disjoint dj] at hh
    have hs := Finset.card_sdiff_add_card_inter Y X
    rw [Finset.inter_comm Y X] at hs
    have hy : Y.card = G.degree y := G.card_neighborFinset_eq_degree y
    change A.card ≤ k+1+(X ∩ Y).card-G.degree y
    omega
  let row (a : V) := T.filter (fun w => G.Adj a w ∧ G.dist x w = G.dist x a+1)
  have rcap (a : V) : (row a).card ≤ k := by
    by_cases hn : (row a).Nonempty
    · obtain ⟨w,hw⟩ := hn
      obtain ⟨ht,_,he⟩ := mem_filter.mp hw
      have hh := (mem_filter.mp ht).2.1
      obtain ⟨b,hb,hab⟩ := predecessor (G := G) (x := x) (z := a) (j := G.dist x a-1) (by omega)
      have hs : insert b (row a) ⊆ E b := by
        intro v hv
        rcases mem_insert.mp hv with rfl | hv
        · exact mem_filter.mpr ⟨mem_univ _,by simp⟩
        · obtain ⟨_,hav,hvlen⟩ := mem_filter.mp hv
          have hlu := hc.dist_triangle (u := b) (v := a) (w := v)
          rw [dist_eq_one_iff_adj.mpr hab,dist_eq_one_iff_adj.mpr hav] at hlu
          have hlo := hc.dist_triangle (u := x) (v := b) (w := v)
          exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
      have hnb : b ∉ row a := by intro h; have := (mem_filter.mp h).2.2; omega
      have hsize := (card_le_card hs).trans (ecap b)
      rw [Finset.card_insert_of_notMem hnb] at hsize
      omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have tr : T ⊆ A.biUnion row := by
    intro w hw
    obtain ⟨hx,hy,ho⟩ := (mem_filter.mp hw).2
    obtain ⟨a,ha,haw⟩ := predecessor (G := G) (x := x) (z := w) (j := G.dist x w-1) (by omega)
    have he : Even (G.dist x a) := by rw [Nat.even_iff] at ho ⊢; omega
    have hna : a ∉ Y := by
      intro h
      have ht := hc.dist_triangle (u := y) (v := a) (w := w)
      rw [dist_eq_one_iff_adj.mpr (yw _ h),dist_eq_one_iff_adj.mpr haw] at ht
      omega
    exact mem_biUnion.mpr ⟨a,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,he⟩,hna⟩,
      mem_filter.mpr ⟨hw,haw,by omega⟩⟩
  have tc : T.card ≤ k*A.card := calc
    T.card ≤ (A.biUnion row).card := card_le_card tr
    _ ≤ ∑ a ∈ A, (row a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, k := Finset.sum_le_sum fun a _ => rcap a
    _ = _ := by simp [Nat.mul_comm]
  have all : univ ⊆ ((E x ∪ E y) ∪ C) ∪ T := by
    intro v _
    by_cases ex : Even (G.dist x v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨mem_univ _,ex⟩)))
    by_cases ey : Even (G.dist y v)
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,ey⟩)))
    have h1 := hc.dist_triangle (u:=x) (v:=y) (w:=v)
    have h2 := hc.dist_triangle (u:=y) (v:=x) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hxy] at h1
    rw [dist_eq_one_iff_adj.mpr hxy.symm] at h2
    have o1 := ex
    have o2 := ey
    rw [Nat.even_iff] at o1 o2
    by_cases large : 3 ≤ G.dist x v
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,large,by omega,ex⟩)
    · have ax : G.dist x v = 1 := by omega
      have ay : G.dist y v = 1 := by omega
      exact mem_union_left _ (mem_union_right _ (mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp ax),
         (G.mem_neighborFinset _ _).mpr (dist_eq_one_iff_adj.mp ay)⟩))
  have total := card_le_card all
  rw [card_univ] at total
  have h1 := Finset.card_union_le (E x) (E y)
  have h2 := Finset.card_union_le (E x ∪ E y) C
  have h3 := Finset.card_union_le ((E x ∪ E y) ∪ C) T
  have mul := Nat.mul_le_mul_left k ac
  have ecx := ecap x
  have ecy := ecap y
  change Fintype.card V ≤ 2*k+2+C.card+k*(k+1+C.card-G.degree y)
  omega

#print axioms edge_order
end Graph189EdgeOrder
