import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite

namespace Graph189DegreeCeiling

open Finset SimpleGraph

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

/-- A vertex of degree at most k and the distance-even cap bound every degree by 3k. -/
theorem degree_le_three_mul_of_distance_two_cap (hc : G.Connected) {k : ℕ}
    (limited : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ k) {z : V} (hz : G.degree z ≤ k) (x : V) :
    G.degree x ≤ 3*k := by
  classical
  let D (v : V) := univ.filter (fun w => G.dist v w = 2)
  have two {v a w : V} (hva : G.Adj v a) (haw : G.Adj a w)
      (hne : v ≠ w) (hn : ¬G.Adj v w) : w ∈ D v := by
    have upper := hc.dist_triangle (u := v) (v := a) (w := w)
    rw [dist_eq_one_iff_adj.mpr hva,dist_eq_one_iff_adj.mpr haw] at upper
    have h0 : G.dist v w ≠ 0 := fun e => hne (hc.dist_eq_zero_iff.mp e)
    have h1 : G.dist v w ≠ 1 := fun e => hn (dist_eq_one_iff_adj.mp e)
    exact mem_filter.mpr ⟨mem_univ _,by omega⟩
  let N := G.neighborFinset x
  have degreeN : N.card = G.degree x := G.card_neighborFinset_eq_degree x
  have bound {A B C : Finset V} (sub : N ⊆ (A ∪ B) ∪ C)
      (a : A.card ≤ k) (b : B.card ≤ k) (c : C.card ≤ k) : G.degree x ≤ 3*k := by
    have h := card_le_card sub
    have h1 := card_union_le A B
    have h2 := card_union_le (A ∪ B) C
    omega
  have hnz : (G.neighborFinset z).card ≤ k := (G.card_neighborFinset_eq_degree z).le.trans hz
  by_cases eq : x = z
  · subst x
    omega
  by_cases adj : G.Adj x z
  · have one : 1 ≤ k := by
      have hsub : {x} ⊆ G.neighborFinset z := singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr adj.symm)
      have h := card_le_card hsub
      simp only [card_singleton] at h
      omega
    apply bound (A := D z) (B := G.neighborFinset z) (C := {z}) _ (limited z) hnz (by simpa using one)
    intro w hw
    have hxw := (G.mem_neighborFinset _ _).mp hw
    by_cases same : z = w
    · exact mem_union_right _ (mem_singleton.mpr same.symm)
    by_cases hzw : G.Adj z w
    · exact mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset _ _).mpr hzw))
    exact mem_union_left _ (mem_union_left _ (two adj.symm hxw same hzw))
  by_cases h2 : G.dist x z = 2
  · obtain ⟨u,hu,huz⟩ := predecessor (j := 1) h2
    have hxu := dist_eq_one_iff_adj.mp hu
    apply bound (A := D u) (B := D z) (C := G.neighborFinset z) _ (limited u) (limited z) hnz
    intro w hw
    have hxw := (G.mem_neighborFinset _ _).mp hw
    by_cases hzw : G.Adj z w
    · exact mem_union_right _ ((G.mem_neighborFinset _ _).mpr hzw)
    by_cases huw : G.Adj u w
    · exact mem_union_left _ (mem_union_right _ (two huz.symm huw (fun e => by subst w; exact adj hxw) hzw))
    exact mem_union_left _ (mem_union_left _ (two hxu.symm hxw (fun e => by subst w; exact hzw huz.symm) huw))
  have d0 : G.dist x z ≠ 0 := fun e => eq (hc.dist_eq_zero_iff.mp e)
  have d1 : G.dist x z ≠ 1 := fun e => adj (dist_eq_one_iff_adj.mp e)
  have reach (gap : ℕ) (t : V) (dt : G.dist x t = 3+gap) : ∃ w, G.dist x w = 3 := by
    induction gap generalizing t with
    | zero => exact ⟨t,by omega⟩
    | succ j ih =>
      obtain ⟨a,ha,_⟩ := predecessor (j := 3+j) (z := t) (by omega)
      exact ih a ha
  obtain ⟨t,ht⟩ := reach (G.dist x z-3) z (by omega)
  obtain ⟨v,hv,hvt⟩ := predecessor (j := 2) ht
  obtain ⟨u,hu,huv⟩ := predecessor (j := 1) hv
  have hxu := dist_eq_one_iff_adj.mp hu
  apply bound (A := D u) (B := D v) (C := D t) _ (limited u) (limited v) (limited t)
  intro w hw
  have hxw := (G.mem_neighborFinset _ _).mp hw
  have dxw := dist_eq_one_iff_adj.mpr hxw
  have hwt : ¬G.Adj t w := by
    intro htw
    have hh := hc.dist_triangle (u := x) (v := w) (w := t)
    rw [dxw,dist_eq_one_iff_adj.mpr htw.symm] at hh
    omega
  by_cases hvw : G.Adj v w
  · exact mem_union_right _ (two hvt.symm hvw (fun e => by subst w; omega) hwt)
  by_cases huw : G.Adj u w
  · exact mem_union_left _ (mem_union_right _ (two huv.symm huw (fun e => by subst w; omega) hvw))
  exact mem_union_left _ (mem_union_left _ (two hxu.symm hxw (fun e => by subst w; exact hvw huv.symm) huw))

#print axioms degree_le_three_mul_of_distance_two_cap

end Graph189DegreeCeiling
