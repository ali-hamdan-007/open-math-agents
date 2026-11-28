import Mathlib.Combinatorics.SimpleGraph.Diam

namespace Graph189SeparatorComparison

open SimpleGraph Finset

private theorem distance_two_of_common_neighbor {V : Type*} {G : SimpleGraph V} {x a y : V}
    (first : G.Adj x a) (second : G.Adj a y) (distinct : x ≠ y) (nonedge : ¬ G.Adj x y) :
    G.dist x y = 2 := by
  let p : G.Walk x y := .cons first (.cons second .nil)
  have hle : G.dist x y ≤ 2 := by simpa [p] using G.dist_le p
  have hpos : G.dist x y ≠ 0 := fun h => distinct ((p.reachable.dist_eq_zero_iff).mp h)
  have hone : G.dist x y ≠ 1 := fun h => nonedge (dist_eq_one_iff_adj.mp h)
  omega

/-- In an expanding component neighborhood, a high vertex adjacent to an anchor
covering another component forces that component to be strictly smaller.
The parts represent components after deletion of the separator. -/
theorem component_size_lt {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj] (parts : I → Finset V)
    (separate : ∀ {i j}, i ≠ j → Disjoint (parts i) (parts j))
    {c d : I} (different : d ≠ c) {x : V} (root : x ∈ parts c)
    (nocross : ∀ i, i ≠ c → ∀ y ∈ parts i, ¬ G.Adj x y)
    (touched : Finset I) (hc : c ∈ touched) (hd : d ∈ touched)
    (expansion : (G.neighborFinset x \ parts c).card + 2 ≤ touched.card)
    (rep : I → V) (contacts : ∀ i ∈ touched, i ≠ c →
      rep i ∈ parts i ∧ ∃ a, G.Adj x a ∧ G.Adj a (rep i))
    (complete : ∃ a, G.Adj x a ∧ ∀ y ∈ parts d, G.Adj a y)
    (budget : (Finset.univ.filter (fun y => G.dist x y = 2)).card ≤ G.degree x) :
    (parts d).card < (parts c).card := by
  classical
  let rest := (touched.erase c).erase d
  have facts (i : I) (hi : i ∈ rest) : i ≠ d ∧ i ≠ c ∧ i ∈ touched := by
    simpa [rest, and_assoc] using hi
  have rep_part (i : I) (hi : i ∈ rest) : rep i ∈ parts i :=
    (contacts i (facts i hi).2.2 (facts i hi).2.1).1
  have inj : Set.InjOn rep (rest : Set I) := by
    intro i hi j hj he
    by_contra hij
    exact Finset.disjoint_left.mp (separate hij) (rep_part i hi) (he ▸ rep_part j hj)
  have disj : Disjoint (rest.image rep) (parts d) := by
    refine Finset.disjoint_left.mpr ?_
    intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.disjoint_left.mp (separate (facts i hi).1) (rep_part i hi)
  have two {i : I} (hi : i ≠ c) {y : V} (hy : y ∈ parts i)
      (conn : ∃ a, G.Adj x a ∧ G.Adj a y) : G.dist x y = 2 := by
    obtain ⟨a,hxa,hay⟩ := conn
    have hxy : x ≠ y := by
      intro e
      exact Finset.disjoint_left.mp (separate hi.symm) root (e ▸ hy)
    exact distance_two_of_common_neighbor hxa hay hxy (nocross i hi y hy)
  have subset : rest.image rep ∪ parts d ⊆ Finset.univ.filter (fun y => G.dist x y = 2) := by
    intro y hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.mp hy with hl | hr
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      exact two (facts i hi).2.1 (rep_part i hi) (contacts i (facts i hi).2.2 (facts i hi).2.1).2
    · obtain ⟨a,hxa,all⟩ := complete
      exact two different hr ⟨a,hxa,all y hr⟩
  have lower := (Finset.card_le_card subset).trans budget
  rw [Finset.card_union_of_disjoint disj, Finset.card_image_of_injOn inj] at lower
  have size_rest : rest.card + 2 = touched.card := by
    have h1 := Finset.card_erase_add_one hc
    have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨different,hd⟩ : d ∈ touched.erase c)
    change ((touched.erase c).erase d).card + 2 = _
    omega
  have internal : G.neighborFinset x ∩ parts c ⊆ (parts c).erase x := by
    intro v hv
    obtain ⟨hn,hp⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset x v).mp hn).ne.symm,hp⟩
  have h_int := Finset.card_le_card internal
  have h_erase := Finset.card_erase_add_one root
  have split := Finset.card_sdiff_add_card_inter (G.neighborFinset x) (parts c)
  rw [G.card_neighborFinset_eq_degree] at split
  omega

#print axioms component_size_lt
end Graph189SeparatorComparison
