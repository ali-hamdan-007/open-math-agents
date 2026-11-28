import Graph189BoundaryMatching

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- The vertices, in the original vertex type, of one genuine connected component
after the support of p has been removed. -/
noncomputable def exteriorComponentSet (p : G.Walk x y)
    (C : (G.induce {v : V | v∉p.support}).ConnectedComponent) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ hv : v∉p.support,
    (G.induce {t : V | t∉p.support}).connectedComponentMk ⟨v,hv⟩ = C)

private theorem component_mem (p : G.Walk x y)
    (C : (G.induce {v : V | v∉p.support}).ConnectedComponent) (v : V) :
    v∈exteriorComponentSet p C ↔ ∃ hv : v∉p.support,
       (G.induce {t : V | t∉p.support}).connectedComponentMk ⟨v,hv⟩=C := by
  classical
  simp [exteriorComponentSet]

theorem actual_component_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (C : (G.induce {v : V | v∉p.support}).ConnectedComponent)
    (size : 1 < (exteriorComponentSet p C).card)
    (hconn : ∀ a b : exteriorComponentSet p C, a≠b →
      ∃ q : (G.induce (exteriorComponentSet p C : Set V)).Walk a b, q.IsHamiltonian)
    {s : ℕ} (positive : 0 < s) (smallP : s ≤ p.support.length)
    (smallC : s ≤ (exteriorComponentSet p C).card)
    (connected : ∀ cut : Finset V, cut.card < s → (G.induce {u : V | u∉cut}).Connected) :
    (s+2)*(exteriorComponentSet p C).card+s ≤ Fintype.card V := by
  classical
  apply whole_core_order_of_connectivity p hp longest (exteriorComponentSet p C)
    (fun z hz => ((component_mem p C z).mp hz).choose) size _ hconn positive smallP smallC connected
  intro u hu v hv edge
  by_contra outside
  obtain ⟨uo,component⟩ := (component_mem p C u).mp hu
  have induced : (G.induce {w : V | w∉p.support}).Adj ⟨u,uo⟩ ⟨v,outside⟩ := edge
  exact hv ((component_mem p C v).mpr
    ⟨outside,(SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj induced).symm.trans component⟩)

#print axioms actual_component_order
end Graph189ExteriorGap
