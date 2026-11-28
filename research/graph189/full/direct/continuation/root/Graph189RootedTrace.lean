import Graph189RootedOreCount
import Graph189RootedPath
import Graph189WedgeCorollary
import Graph189R1Metric

namespace Graph189RootedTrace
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A local Ore bound away from a single prescribed vertex gives a spanning
path starting at that vertex. -/
theorem rooted_local_ore (hc : G.Connected) (z : V)
    (ore : ∀ {u w v : V}, u ≠ z → v ≠ z → G.Adj u w → G.Adj w v → ¬G.Adj u v →
      (G.neighborFinset u ∪ G.neighborFinset w ∪ G.neighborFinset v).card ≤
        G.degree u + G.degree v) :
    ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  obtain ⟨v,P,hp,longest⟩ := Graph189RootedPath.exists_rooted_longest G z
  refine ⟨v,P,hp.isHamiltonian_iff.mpr ?_⟩
  intro x
  by_contra hx
  obtain ⟨u,hu,hcP⟩ := Graph189RootedPath.exists_exterior_contact P hc ⟨x,hx⟩
  obtain ⟨W,succ,hn,hi,ht,hm,ha,hc',hs,huz⟩ :=
    Graph189RootedPath.successors_of_rooted_longest P hp longest hu hcP
  obtain ⟨w,hw,hbad⟩ := Graph189RootedOreCount.bad_wedge_of_successors u W succ hn hi ht hm ha hc'
  exact (not_lt_of_ge (ore huz (hs _ hw).2 (ht _ hw) (hs _ hw).1 (hm _ hw).2)) hbad

/-- Original Graph 189 invariants. Above the stated order, there is a spanning
path from a vertex of minimum degree. The imported degree-pair lemma is from
the project's merged R1 reduction. -/
theorem of_order [Nontrivial V] (hc : G.Connected)
    (hcap : (univ.image (distEven G)).max' (by simp) ≤ 1 + G.secondSmallestDegree)
    (large : (3+(G.maxDegree-G.secondSmallestDegree))*G.secondSmallestDegree+1 < Fintype.card V) :
    ∃ z, G.degree z = G.minDegree ∧ ∃ v, ∃ p : G.Walk z v, p.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have high (u : V) (hu : u ≠ z) : G.secondSmallestDegree ≤ G.degree u := by
    rcases OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G := G) u z hu with h|h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree u)
  have cap (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    have hb := (le_max' _ _ (mem_image_of_mem (distEven G) (mem_univ v))).trans hcap
    omega
  refine ⟨z,hz.symm,rooted_local_ore hc z ?_⟩
  intro u w v hu hv eu ev huv
  have hmax := G.degree_le_maxDegree w
  have highu := high u hu
  have highv := high v hv
  have hm := G.degree_le_maxDegree u
  have e := cap w
  have hbound : G.degree w + G.distEven w ≤
      G.degree u + G.degree v + (G.maxDegree-G.secondSmallestDegree) + 1 := by omega
  have loc := Graph189WedgeOrder.local_ore_of_order hc eu.symm ev huv cap hbound large
  simpa only [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using loc

#print axioms rooted_local_ore
#print axioms of_order
end Graph189RootedTrace
