import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Graph40

open SimpleGraph

/-- A bipartite graph with at most one non-leaf neighbor at every vertex of one
side is a forest. In a cycle each neighbor along the cycle is non-leaf. -/
theorem isAcyclic_of_left_two_hop {V : Type*} {G : SimpleGraph V} (X : Set V)
    (cross : ∀ {x y}, G.Adj x y → (x ∈ X ↔ y ∉ X))
    (hle : ∀ x ∈ X, ∀ y z, G.Adj x y → G.Adj x z →
      (∃ u, u ≠ x ∧ G.Adj y u) → (∃ v, v ≠ x ∧ G.Adj z v) → y = z) :
    G.IsAcyclic := by
  intro a walk hcycle
  classical
  let C := walk.toSubgraph.spanningCoe
  have hcyc : C.IsCycles := hcycle.isCycles_spanningCoe_toSubgraph
  have hsub {a b : V} (hab : C.Adj a b) : G.Adj a b := walk.toSubgraph.adj_sub hab
  have hstart : C.Adj a walk.snd := by
    exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
      (walk.mk_start_snd_mem_edges hcycle.not_nil)
  have elim {x y : V} (hx : x ∈ X) (hxy : C.Adj x y) : False := by
    obtain ⟨z, hyz, hxz⟩ := hcyc.other_adj_of_adj hxy
    obtain ⟨u, hxu, hyu⟩ := hcyc.other_adj_of_adj hxy.symm
    obtain ⟨v, hxv, hzv⟩ := hcyc.other_adj_of_adj hxz.symm
    exact hyz (hle x hx y z (hsub hxy) (hsub hxz)
      ⟨u, hxu.symm, hsub hyu⟩ ⟨v, hxv.symm, hsub hzv⟩)
  by_cases ha : a ∈ X
  · exact elim ha hstart
  · exact elim (by by_contra hn; exact ha ((cross (hsub hstart)).mpr hn)) hstart.symm

/-- An ordered version of the two-hop forest criterion. The highest-ranked left
vertex of a cycle sees two different two-hop connections to earlier left vertices. -/
theorem isAcyclic_of_ranked_left_two_hop {V : Type*} {G : SimpleGraph V} (X : Set V)
    (rank : V → ℕ) (hrank : Set.InjOn rank X)
    (cross : ∀ {x y}, G.Adj x y → (x ∈ X ↔ y ∉ X))
    (hle : ∀ x ∈ X, ∀ y z, G.Adj x y → G.Adj x z →
      (∃ u ∈ X, rank u < rank x ∧ G.Adj y u) →
        (∃ v ∈ X, rank v < rank x ∧ G.Adj z v) → y = z) :
    G.IsAcyclic := by
  intro a walk hcycle
  classical
  let C := walk.toSubgraph.spanningCoe
  have hcyc : C.IsCycles := hcycle.isCycles_spanningCoe_toSubgraph
  have hsub {u v : V} (huv : C.Adj u v) : G.Adj u v := walk.toSubgraph.adj_sub huv
  have hstart : C.Adj a walk.snd :=
    SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr
      (walk.mk_start_snd_mem_edges hcycle.not_nil)
  have seen {u v : V} (huv : C.Adj u v) : u ∈ walk.support :=
    walk.mem_verts_toSubgraph.mp (walk.toSubgraph.edge_vert huv)
  let xs := walk.support.toFinset.filter (· ∈ X)
  have hxs : xs.Nonempty := by
    by_cases ha : a ∈ X
    · exact ⟨a, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (seen hstart), ha⟩⟩
    · have hs : walk.snd ∈ X := by
        by_contra hn
        exact ha ((cross (hsub hstart)).mpr hn)
      exact ⟨walk.snd, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (seen hstart.symm), hs⟩⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image xs rank hxs
  obtain ⟨hxsupp, hxX⟩ := Finset.mem_filter.mp hx
  have hxsupp' : x ∈ walk.support := List.mem_toFinset.mp hxsupp
  obtain ⟨e, he, hxe⟩ :=
    (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hcycle.not_nil).mp hxsupp'
  obtain ⟨y, hxy⟩ : ∃ y, C.Adj x y := by
    revert he hxe
    refine Sym2.inductionOn e ?_
    intro s t he hxe
    have hst : C.Adj s t := SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he
    rcases Sym2.mem_iff.mp hxe with h | h
    · exact ⟨t, h ▸ hst⟩
    · exact ⟨s, h ▸ hst.symm⟩
  obtain ⟨z, hyz, hxz⟩ := hcyc.other_adj_of_adj hxy
  have earlier {w : V} (hxw : C.Adj x w) :
      ∃ u ∈ X, rank u < rank x ∧ G.Adj w u := by
    obtain ⟨u, hxu, hwu⟩ := hcyc.other_adj_of_adj hxw.symm
    have hw : w ∉ X := (cross (hsub hxw)).mp hxX
    have hu : u ∈ X := (cross (hsub hwu.symm)).mpr hw
    have humem : u ∈ xs :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (seen hwu.symm), hu⟩
    refine ⟨u, hu, lt_of_le_of_ne (hmax u humem) ?_, hsub hwu⟩
    intro he
    exact hxu (hrank hu hxX he).symm
  exact hyz (hle x hxX y z (hsub hxy) (hsub hxz) (earlier hxy) (earlier hxz))

#print axioms isAcyclic_of_left_two_hop
#print axioms isAcyclic_of_ranked_left_two_hop

end Graph40
