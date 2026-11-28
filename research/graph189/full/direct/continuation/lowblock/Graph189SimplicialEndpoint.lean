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

/-- At even order at least six, Dirac degree with at most two vertices
attaining equality gives a spanning path between any specified endpoints. -/
theorem prescribed_of_two_exceptions {d : ℕ} (order : Fintype.card V=2*d) (three : 3 ≤ d)
    (half : ∀ v, d ≤ G.degree v) (L : Finset V) (few : L.card≤2)
    (better : ∀ v∉L, d < G.degree v) (x y : V) (ne : x≠y) :
    ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  let K : SimpleGraph V := {
    Adj a b := G.Adj a b ∨ (a≠b ∧ (a∉L ∨ b∉L))
    symm := ⟨fun _ _ h => h.elim (fun e => Or.inl e.symm)
      (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)⟩
    loopless := ⟨fun a h => h.elim (G.irrefl) (fun h => h.1 rfl)⟩ }
  have incl : G ≤ K := fun _ _ h => Or.inl h
  apply prescribed_of_supergraph (H:=K) incl
  · intro a b h missing
    obtain ⟨_,ha|hb⟩ := h.resolve_left missing
    · have := better a ha
      have := half b
      omega
    · have := better b hb
      have := half a
      omega
  apply prescribed_of_supergraph (H:=⊤) le_top _ (complete_prescribed x y ne)
  intro a b hab missing
  have inA : a∈L := by by_contra h; exact missing (Or.inr ⟨hab.ne,Or.inl h⟩)
  have inB : b∈L := by by_contra h; exact missing (Or.inr ⟨hab.ne,Or.inr h⟩)
  have near (v : V) (inside : v∈L) : (Lᶜ : Finset V).card ≤ K.degree v := by
    apply card_le_card
    intro z hz
    have out := mem_compl.mp hz
    exact (K.mem_neighborFinset _ _).mpr (Or.inr ⟨fun h => out (h ▸ inside),Or.inr out⟩)
  have x1 := near a inA
  have x2 := near b inB
  rw [card_compl] at x1 x2
  omega

#print axioms prescribed_of_two_exceptions
#print axioms prescribed_of_simplicial
end Graph189TerminalLeafClosure
