import Graph189SeparatorCover

open Finset SimpleGraph
namespace Graph189HighPredecessor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Both endpoints and both open neighborhoods fit in the closed two-ball of
the center of an induced wedge. -/
theorem common_lower {a b z : V} (hab : a ≠ b) (hna : ¬ G.Adj a b)
    (hza : G.Adj z a) (hzb : G.Adj z b) {k : ℕ}
    (cap : G.distEven z ≤ k+1) :
    G.degree a + G.degree b + 1 ≤ G.degree z + k +
      (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  let U := G.neighborFinset a ∪ G.neighborFinset b
  let E := univ.filter (fun v => Even (G.dist z v))
  have inside {v u : V} (hzu : G.Adj z u) (huv : G.Adj u v) :
      v ∈ G.neighborFinset z ∪ E := by
    by_cases hzv : G.Adj z v
    · exact mem_union_left _ ((G.mem_neighborFinset z v).mpr hzv)
    apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    by_cases he : z = v
    · subst v; simp
    let path : G.Walk z v := .cons hzu (.cons huv .nil)
    have hlo := path.reachable.one_lt_dist_of_ne_of_not_adj he hzv
    have hhi : G.dist z v ≤ 2 := G.dist_le path
    have : G.dist z v = 2 := by omega
    simp [this]
  have cover : insert a (insert b U) ⊆ G.neighborFinset z ∪ E := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hza)
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hzb)
    rcases mem_union.mp hv with hv | hv
    · exact inside hza ((G.mem_neighborFinset _ _).mp hv)
    · exact inside hzb ((G.mem_neighborFinset _ _).mp hv)
  have ha : a ∉ U := by
    intro hv
    rcases mem_union.mp hv with hv | hv
    · exact G.loopless.irrefl a ((G.mem_neighborFinset _ _).mp hv)
    · exact hna ((G.mem_neighborFinset _ _).mp hv).symm
  have hb : b ∉ U := by simp [U, hna]
  have ha' : a ∉ insert b U := by simp [hab,ha]
  have hsize := (card_le_card cover).trans (card_union_le (G.neighborFinset z) E)
  rw [card_insert_of_notMem ha',card_insert_of_notMem hb,G.card_neighborFinset_eq_degree] at hsize
  have he : E.card ≤ k+1 := cap
  have hu := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at hu
  change U.card + _ = _ at hu
  omega

/-- A subthreshold common neighbor between high, nonadjacent vertices always
has a different common neighbor. Under the second-degree hypothesis it is high. -/
theorem another_common {a b z : V} (hab : a ≠ b) (hna : ¬ G.Adj a b)
    (hza : G.Adj z a) (hzb : G.Adj z b) {k : ℕ}
    (cap : G.distEven z ≤ k+1) (ha : k ≤ G.degree a) (hb : k ≤ G.degree b)
    (hz : G.degree z < k) :
    ∃ w ≠ z, G.Adj a w ∧ G.Adj b w := by
  classical
  have count := common_lower hab hna hza hzb cap
  by_contra! bad
  have only : G.neighborFinset a ∩ G.neighborFinset b ⊆ {z} := by
    intro w hw
    obtain ⟨wa,wb⟩ := mem_inter.mp hw
    apply mem_singleton.mpr
    by_contra ne
    exact bad w ne ((G.mem_neighborFinset _ _).mp wa) ((G.mem_neighborFinset _ _).mp wb)
  have hle := card_le_card only
  rw [card_singleton] at hle
  omega

#print axioms common_lower
#print axioms another_common
end Graph189HighPredecessor
