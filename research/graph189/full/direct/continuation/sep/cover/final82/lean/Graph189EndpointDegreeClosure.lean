import Graph189ExteriorClosure

open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A prescribed endpoint has its additional pendant edge in the augmented graph. -/
theorem endpoint_degree_gain (G : SimpleGraph V) [DecidableRel G.Adj] (u v a : V)
    (endpoint : a=u ∨ a=v) :
    G.degree a+1 ≤ (terminalLeaves G u v).degree (.inl a) := by
  classical
  obtain ⟨l,attached⟩ : ∃ l : Bool, (terminalLeaves G u v).Adj (.inl a) (.inr l) := by
    rcases endpoint with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let core := (G.neighborFinset a).image (Sum.inl : V → V⊕Bool)
  have absent : Sum.inr l∉core := by simp [core]
  have incl : insert (.inr l) core ⊆ (terminalLeaves G u v).neighborFinset (.inl a) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hc
    · exact ((terminalLeaves G u v).mem_neighborFinset _ _).mpr attached
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
      simp only [SimpleGraph.mem_neighborFinset] at hb ⊢
      exact hb
  have count := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem absent,show core.card=G.degree a from
    Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at count
  exact count

/-- A missing edge incident to a prescribed endpoint has threshold n, one
less than the ordinary Hamilton-connected closure threshold. -/
theorem prescribed_of_incident_edge {G : SimpleGraph V} [DecidableRel G.Adj] {u v a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (incident : (a=u ∨ a=v) ∨ (b=u ∨ b=v))
    (degree : Fintype.card V ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  have aug := leaf_traceable_of_prescribed hp
  rw [terminalLeaves_sup_edge] at aug
  apply prescribed_of_leaf_traceable
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => distinct (Sum.inl.inj h)
  · exact missing
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum,Fintype.card_bool]
    rcases incident with atA | atB
    · have := endpoint_degree_gain G u v a atA
      omega
    · have := endpoint_degree_gain G u v b atB
      omega
  · exact aug

theorem add_edge_degree_gain (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V} (distinct : a≠b)
    (missing : ¬G.Adj a b) : G.degree a+1 ≤ (G⊔edge a b).degree a := by
  classical
  have inc : insert b (G.neighborFinset a) ⊆ (G⊔edge a b).neighborFinset a := by
    intro z hz
    simp only [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_insert.mp hz with rfl | inside
    · exact Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,distinct⟩)
    · exact Or.inl ((G.mem_neighborFinset _ _).mp inside)
  have card := Finset.card_le_card inc
  rw [Finset.card_insert_of_notMem (fun h => missing ((G.mem_neighborFinset _ _).mp h))] at card
  exact card

#print axioms prescribed_of_incident_edge
end Graph189TerminalLeafClosure
