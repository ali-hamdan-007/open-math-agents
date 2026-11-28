import Graph189EndpointDegreeClosure

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Distinct prescribed endpoints admit a Hamilton path when all vertices except
z have degree at least (n+1)/2, z has degree at least two, and the endpoints
are not both neighbors of z. -/
theorem prescribed_avoiding_low_neighbors {G : SimpleGraph V} [DecidableRel G.Adj]
    (z u v : V) (distinct : u≠v) (low_degree : 2≤G.degree z)
    (high : ∀ a, a≠z → Fintype.card V+1 ≤ 2*G.degree a)
    (avoids : ¬(G.Adj z u ∧ G.Adj z v)) : ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  let W := Finset.univ.erase z
  let H := G⊔fillInside W
  have inc : G≤H := le_sup_left
  apply prescribed_of_supergraph inc
  · intro a b adj missing
    rcases adj with h | h
    · exact (missing h).elim
    · have := high a (Finset.mem_erase.mp h.1).1
      have := high b (Finset.mem_erase.mp h.2.1).1
      omega
  have same (a : V) (h : H.Adj z a) : G.Adj z a := by
    rcases h with h | h
    · exact h
    · exact (Finset.notMem_erase _ _ h.1).elim
  by_cases all : ∀ t, t≠z → H.Adj z t
  · have eq : H=⊤ := by
      apply le_antisymm le_top
      intro a b hab
      have ab := (top_adj _ _).mp hab
      by_cases az : a=z
      · subst a
        exact all b ab.symm
      by_cases bz : b=z
      · subst b
        exact (all a az).symm
      · exact Or.inr ⟨by simp [W,az],by simp [W,bz],ab⟩
    rw [eq]
    exact complete_prescribed u v distinct
  push Not at all
  obtain ⟨q,qz,qmiss⟩ := all
  obtain ⟨t,tz,missing,incident⟩ : ∃ t, t≠z ∧ ¬H.Adj z t ∧
      ((z=u ∨ z=v) ∨ (t=u ∨ t=v)) := by
    by_cases zu : z=u
    · exact ⟨q,qz,qmiss,Or.inl (Or.inl zu)⟩
    by_cases zv : z=v
    · exact ⟨q,qz,qmiss,Or.inl (Or.inr zv)⟩
    by_cases hn : H.Adj z u
    · exact ⟨v,Ne.symm zv,fun hv => avoids ⟨same u hn,same v hv⟩,Or.inr (Or.inr rfl)⟩
    · exact ⟨u,Ne.symm zu,hn,Or.inr (Or.inl rfl)⟩
  have tW : t∈W := by simp [W,tz]
  have subset : W.erase t ⊆ H.neighborFinset t := by
    intro a ha
    obtain ⟨diff,inside⟩ := Finset.mem_erase.mp ha
    exact (H.mem_neighborFinset _ _).mpr (Or.inr ⟨tW,inside,diff.symm⟩)
  have d := Finset.card_le_card subset
  rw [Finset.card_erase_of_mem tW,SimpleGraph.card_neighborFinset_eq_degree] at d
  have wc : W.card=Fintype.card V-1 := by simp [W,Finset.card_erase_of_mem]
  have dz := low_degree.trans (degree_le_of_le (v:=z) inc)
  let J := H⊔edge z t
  have hj : H≤J := le_sup_left
  have gain := add_edge_degree_gain H tz.symm missing
  have z3 : 3≤J.degree z := by change 3≤(H⊔edge z t).degree z; omega
  have large := J.degree_lt_card_verts z
  have hjhigh (a : V) (az : a≠z) : Fintype.card V+1≤2*J.degree a := by
    have := high a az
    have := degree_le_of_le (v:=a) (inc.trans hj)
    omega
  apply prescribed_of_incident_edge tz.symm missing incident (by omega)
  apply exterior_one_low z u v distinct _ hjhigh
  intro a
  by_cases az : a=z
  · subst a
    exact z3
  · have := hjhigh a az
    omega

#print axioms prescribed_avoiding_low_neighbors
end Graph189TerminalLeafClosure
