import Graph189RootedPath
import Graph189WedgeOrder

namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset

/-- Closing the longest initial segment ending at a neighbor of the same endpoint
gives a cycle with at least one more vertex than the graph's minimum degree. -/
theorem cycle_of_degree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (z : V) {d : ℕ} (two : 2 ≤ d) (degree : ∀ v, d ≤ G.degree v) :
    ∃ y, ∃ Q : G.Walk y y, Q.IsCycle ∧ d+1 ≤ Q.length := by
  obtain ⟨x,P,hp,maximal⟩ := Graph189RootedPath.exists_rooted_longest G z
  let R := P.reverse
  have all (v : V) (adj : G.Adj x v) : v ∈ R.support := by
    by_contra outside
    have absent : v ∉ P.support := by simpa [R] using outside
    have extended := maximal (P.concat adj) (hp.concat absent adj)
    simp at extended
  let U := (R.support.take d).toFinset
  have first : x ∈ U := by
    apply List.mem_toFinset.mpr
    apply (List.mem_take_iff_idxOf_lt R.start_mem_support).mpr
    have idx := R.length_takeUntil R.start_mem_support
    simp at idx
    omega
  have small : (U.erase x).card < d := by
    have one := card_erase_add_one first
    have le := List.toFinset_card_le (R.support.take d)
    have len := List.length_take_le d R.support
    change U.card ≤ _ at le
    omega
  have outside : ∃ v ∈ G.neighborFinset x, v ∉ U := by
    by_contra! h
    have sub : G.neighborFinset x ⊆ U.erase x :=
      fun v hv => mem_erase.mpr ⟨((G.mem_neighborFinset x v).mp hv).ne.symm,h v hv⟩
    have bound := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at bound
    have := degree x
    omega
  obtain ⟨y,adj,far⟩ := outside
  have edge := (G.mem_neighborFinset x y).mp adj
  have hy := all y edge
  let T := R.takeUntil y hy
  have farIndex : d ≤ R.support.idxOf y := by
    by_contra! h
    exact far (List.mem_toFinset.mpr ((List.mem_take_iff_idxOf_lt hy).mpr h))
  have long : d ≤ T.length := by rwa [R.length_takeUntil hy]
  refine ⟨y,T.cons edge.symm,?_,by simp only [Walk.length_cons]; omega⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_,by simp only [Walk.length_cons]; omega⟩
  rw [Walk.tail_cons]
  exact (Walk.isPath_copy _ _ _).mpr (hp.reverse.takeUntil hy)

/-- Exact distance two is inherited by every induced subgraph in the direction
needed to charge distance-two witnesses to the original graph. -/
theorem original_dist_two {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : S} (two : (G.induce S).dist x y = 2) : G.dist x.val y.val = 2 := by
  have hr : (G.induce S).Reachable x y := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨P,len⟩ := hr.exists_walk_length_eq_dist
  let f := (Embedding.induce (G:=G) S).toHom
  let W := P.map f
  have le := G.dist_le W
  rw [Walk.length_map,len,two] at le
  have ne : x.val ≠ y.val := by
    intro eq
    rw [Subtype.ext eq,dist_self] at two
    omega
  have na : ¬G.Adj x.val y.val := by
    intro h
    have ha : (G.induce S).Adj x y := h
    rw [dist_eq_one_iff_adj.mpr ha] at two
    omega
  have gt := W.reachable.one_lt_dist_of_ne_of_not_adj ne na
  change 1 < G.dist x.val y.val at gt
  exact Nat.le_antisymm le (by omega)

noncomputable def exactTwo {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist x v = 2)

/-- The exact second layer in the induced graph fits the ambient positive-even
budget, also when deletion disconnects the graph. -/
theorem induced_second_layer {V : Type*} [Fintype V] {G : SimpleGraph V} (S : Set V)
    [Fintype S] (x : S) {k : ℕ} (cap : G.distEven x.val ≤ k+1) :
    (exactTwo (G.induce S) x).card ≤ k := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let T := (exactTwo (G.induce S) x).map f
  have two : ∀ v ∈ T, G.dist x.val v = 2 := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
    exact original_dist_two (Finset.mem_filter.mp hu).2
  have missing : x.val ∉ T := by
    intro hx
    have h := two _ hx
    simp at h
  have sub : insert x.val T ⊆ univ.filter (fun y => Even (G.dist x.val y)) := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [two v h]
      decide
  have cmp := card_le_card sub
  rw [card_insert_of_notMem missing] at cmp
  have ct : T.card = (exactTwo (G.induce S) x).card := card_map _
  change T.card + 1 ≤ G.distEven x.val at cmp
  omega

#print axioms cycle_of_degree
#print axioms original_dist_two
#print axioms induced_second_layer
end Graph189ExteriorDegreeCycle
