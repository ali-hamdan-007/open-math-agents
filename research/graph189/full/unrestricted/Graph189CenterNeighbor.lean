import Graph189LocalOre

open SimpleGraph Finset Graph189LocalOre
namespace Graph189CenterNeighbor

variable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A radius-two center next to a vertex of degree d bounds the entire
graph by 2k+d+1. Even vertices beyond the second layer at the latter
vertex give a further improvement. -/
theorem center_neighbor_order (connected : G.Connected) (k : ℕ)
    (cap : ∀ v, G.distEven v ≤ 1 + k) {x c : V} (edge : G.Adj x c)
    (center : ∀ y, G.dist c y ≤ 2) :
    Fintype.card V + (farEven G x).card ≤ 1 + G.degree x + 2*k := by
  classical
  have center_all : ballTwo G c = univ := by
    ext y
    simp [ballTwo, center]
  have cball := ball_budget connected k cap c
  rw [center_all, card_univ] at cball
  have contain : insert c (G.neighborFinset c) ⊆ ballTwo G x := by
    intro y hy
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rcases mem_insert.mp hy with rfl | hy
    · exact (dist_eq_one_iff_adj.mpr edge).le.trans (by decide)
    · have adj := (G.mem_neighborFinset _ _).mp hy
      let walk : G.Walk x y := .cons edge (.cons adj .nil)
      exact G.dist_le walk
  have cs := card_le_card contain
  have nc : c ∉ G.neighborFinset c := by simp
  rw [card_insert_of_notMem nc] at cs
  change G.degree c + 1 ≤ (ballTwo G x).card at cs
  have xball := ball_budget connected k cap x
  omega

end Graph189CenterNeighbor

#print axioms Graph189CenterNeighbor.center_neighbor_order
