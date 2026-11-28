import Graph189EndpointDegreeClosure

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- In a Dirac graph a vertex whose neighbors form a clique can be prescribed
as one endpoint of a Hamiltonian path to any other vertex. -/
theorem prescribed_of_simplicial (x y : V) (ne : x≠y)
    (half : ∀ v, Fintype.card V ≤ 2*G.degree v)
    (clique : ∀ a b, G.Adj x a → G.Adj x b → a≠b → G.Adj a b) :
    ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G≤J → ∃ p : J.Walk x y, p.IsHamiltonian by
    exact all G le_rfl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro incl
    by_cases universal : ∀ a, x≠a → J.Adj x a
    · apply prescribed_of_supergraph (H:=⊤) le_top _ (complete_prescribed x y ne)
      intro a b hab missing
      have ax : x≠a := by rintro rfl; exact missing (universal b hab.ne)
      have bx : x≠b := by rintro rfl; exact missing (universal a hab.ne.symm).symm
      have gain (v : V) (dv : x≠v) (old : ¬G.Adj x v) : G.degree v+1 ≤ J.degree v := by
        have sub : insert x (G.neighborFinset v) ⊆ J.neighborFinset v := by
          intro z hz
          rcases mem_insert.mp hz with rfl|h
          · exact (J.mem_neighborFinset _ _).mpr (universal v dv).symm
          · exact (J.mem_neighborFinset _ _).mpr (incl ((G.mem_neighborFinset _ _).mp h))
        have count := card_le_card sub
        rw [card_insert_of_notMem (fun h => old ((G.mem_neighborFinset _ _).mp h).symm)] at count
        exact count
      have da := degree_le_of_le (v:=a) incl
      have db := degree_le_of_le (v:=b) incl
      have ha := half a
      have hb := half b
      by_cases old : G.Adj x a
      · have lost : ¬G.Adj x b := fun h => missing (incl (clique a b old h hab.ne))
        have := gain b bx lost
        omega
      · have := gain a ax old
        omega
    · push_neg at universal
      obtain ⟨a,ax,missing⟩ := universal
      have strict : J < J⊔edge x a := by
        apply lt_of_le_of_ne le_sup_left
        intro same
        have added : (J⊔edge x a).Adj x a :=
          Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,ax⟩)
        exact missing (same.symm ▸ added)
      have dx := degree_le_of_le (v:=x) incl
      have da := degree_le_of_le (v:=a) incl
      have hx := half x
      have ha := half a
      exact prescribed_of_incident_edge ax missing (Or.inl (Or.inl rfl)) (by omega)
        (ih _ strict (incl.trans le_sup_left))

#print axioms prescribed_of_simplicial
end Graph189TerminalLeafClosure
