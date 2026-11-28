import Graph189DenseTerminal

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In the unresolved order window a genuine path missing at most k−2 vertices
suffices, also when the graph has a separating pair. -/
theorem traceable_of_near_degree (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (lo : 7≤G.secondSmallestDegree) (upper : Fintype.card V≤5*G.secondSmallestDegree-5)
    (minimum : 3≤G.minDegree) {x y : V} (r : G.Walk x y) (hr : r.IsPath)
    (near : Fintype.card V+2≤r.support.length+G.secondSmallestDegree) :
    ∃a b,∃Q : G.Walk a b,Q.IsHamiltonian := by
  classical
  by_contra bad
  obtain ⟨a,b,p,C,h⟩ := choose hc cap (by omega) minimum bad
  have mx := h.longest r hr
  have lp := p.length_support
  have lr := r.length_support
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup h.path.support_nodup] at total
  have small : p.support.toFinsetᶜ.card+2≤G.secondSmallestDegree := by omega
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have quota := Graph189OrdinaryPathGap.second_layer_budget point
  have unique (u v : V) (hu : G.degree u<G.secondSmallestDegree) (hv : G.degree v<G.secondSmallestDegree) : u=v := by
    by_contra ne
    exact (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne).elim
      (Nat.not_le_of_gt hu) (Nat.not_le_of_gt hv)
  have min (v : V) := minimum.trans (G.minDegree_le_degree v)
  have sub : C⊆p.support.toFinsetᶜ := fun v vc => mem_compl.mpr (fun on => h.outside _ vc (List.mem_toFinset.mp on))
  have lim := card_le_card sub
  apply no_dense_component h _ lo upper (Or.inr small) quota min unique
  · by_contra! short
    exact bad (Graph189OrdinaryPathGap.traceable_of_near_unrestricted hc point (by omega) minimum p h.path short)
  · intro v vc high
    have hf := (internal_half h vc high (quota _) min unique)
    omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.traceable_of_near_degree
