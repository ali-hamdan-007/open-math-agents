import Graph189LeafStrip

open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}

def oldEmbedding (G : SimpleGraph V) (u v : V) : G →g terminalLeaves G u v where
  toFun := Sum.inl
  map_rel' := fun h => h

theorem leaf_traceable_of_prescribed {p : G.Walk u v} (hp : p.IsHamiltonian) :
    ∃ x y, ∃ q : (terminalLeaves G u v).Walk x y, q.IsHamiltonian := by
  let h₁ : (terminalLeaves G u v).Adj (.inr false) (.inl u) := rfl
  let h₂ : (terminalLeaves G u v).Adj (.inl v) (.inr true) := rfl
  let q := Walk.cons h₁ ((p.map (oldEmbedding G u v)).concat h₂)
  have qs : q.support = Sum.inr false :: (p.support.map Sum.inl ++ [Sum.inr true]) := by
    simp [q,oldEmbedding]
    intro a ha
    rfl
  have mapped : (p.support.map (Sum.inl : V → V⊕Bool)).Nodup :=
    hp.isPath.support_nodup.map (fun _ _ h => Sum.inl.inj h)
  have nd : q.support.Nodup := by
    rw [qs]
    simp [List.nodup_append',mapped]
  refine ⟨_,_,q,(Walk.IsPath.mk' nd).isHamiltonian_of_mem ?_⟩
  intro w
  rw [qs]
  cases w with
  | inl z => simp [hp.mem_support z]
  | inr l => cases l <;> simp

theorem prescribed_of_sup_edge [Fintype V] [DecidableRel G.Adj] {a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  exact prescribed_of_leaf_traceable (leaf_traceable_of_core_edge G u v a b distinct missing degree
    (leaf_traceable_of_prescribed hp))

#print axioms prescribed_of_sup_edge
end Graph189TerminalLeafClosure
