import Graph189LeafStructure
import Graph189TraceClosure

namespace Graph189Leaf
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- DeLaViña's condition guarantees traceability for diameter at most three
when the minimum degree is one. Saturate by the path closure theorem, then
use the two even-distance budgets at the leaf and its unique neighbor. -/
theorem traceable_minDegree_one (hc : G.Connected) (hd : G.diam ≤ 3)
    (hm : G.minDegree = 1) (hσ : ∀ x, G.distEven x ≤ 1 + G.secondSmallestDegree) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have hz1 : G.degree z = 1 := hz.symm.trans hm
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (show (G.neighborFinset z).card = 1 by
    rwa [card_neighborFinset_eq_degree])
  have hzv : G.Adj z v := (G.mem_neighborFinset _ _).mp (by simp [hv])
  have hdeg (x : V) (hne : x ≠ z) : G.secondSmallestDegree ≤ G.degree x := by
    have h := Graph189Bipartite.degree_pair (G := G) x z hne
    have hp := G.minDegree_le_degree x
    omega
  obtain ⟨A,B,ha,hb,hA,hB,hn,hdv⟩ := leaf_layers hc hd hσ hv
  let T (K : SimpleGraph V) := ∃ a b : V, ∃ p : K.Walk a b, p.IsHamiltonian
  change T G
  by_contra hno
  obtain ⟨H,hsub,hmax⟩ := Finite.exists_le_maximal (p := fun K => ¬ T K) hno
  apply hmax.prop
  apply traceable_saturated_leaf hsub _ hzv hdeg A B ha hb hA hB hn hdv
  intro x y hne hsum
  by_contra hxy
  have hnot : ¬ T (H ⊔ SimpleGraph.edge x y) := fun hp =>
    hmax.prop (Graph189.traceable_of_sup_edge hne hxy hsum hp)
  have he := hmax.le_of_ge hnot le_sup_left
  exact hxy (he (Or.inr ((SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hne⟩)))

#print axioms traceable_minDegree_one
end Graph189Leaf
