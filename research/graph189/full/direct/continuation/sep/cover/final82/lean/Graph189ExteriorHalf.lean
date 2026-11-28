import Graph189HighExteriorDegree
import Graph189SingleExteriorShift
import Graph189MatchedOrder

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}

/-- Every high omitted vertex of an arbitrary longest path retains half its degree
off that path under the parent hypotheses in the minimum-degree-three range. -/
theorem high_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) {k : ℕ}
    (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  apply nonisolated_exterior_half p hp longest ha _ quota high minimum uniqueLow
  by_contra! empty
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [empty,Finset.card_empty,zero_add] at parts
  have num := contact_card_neighbors p hp a
  have min := minimum a
  change 3 ≤ (G.neighborFinset a).card at min
  have touch : (contactPositions p a).Nonempty := Finset.card_pos.mp (by omega)
  have shift := single_positions_lt_path_shell p hp longest ha touch
  have sub : p.support.toFinset.filter (fun z => G.dist a z=2) ⊆
      Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
  have size := (Finset.card_le_card sub).trans quota
  change k ≤ (G.neighborFinset a).card at high
  omega

/-- Each real high vertex omitted by a longest path forces at least ceil(k/2)+1
vertices to be omitted by that same path. -/
theorem high_outside_order_gap (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) {k : ℕ}
    (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    p.support.length + (k+1)/2 + 1 ≤ Fintype.card V := by
  classical
  let E := G.neighborFinset a \ p.support.toFinset
  have deg := (high_exterior_half p hp longest ha quota high minimum uniqueLow).2
  change G.degree a ≤ 2*E.card at deg
  have fresh : a∉E := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp h).1)
  have outside : ∀ z∈insert a E, z∉p.support := by
    intro z hz onPath
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact ha onPath
    · exact (Finset.mem_sdiff.mp h).2 (List.mem_toFinset.mpr onPath)
  have total := card_outside_add_path p hp (insert a E) outside
  rw [Finset.card_insert_of_notMem fresh] at total
  omega

#print axioms high_exterior_half
#print axioms high_outside_order_gap
end Graph189ExteriorGap
