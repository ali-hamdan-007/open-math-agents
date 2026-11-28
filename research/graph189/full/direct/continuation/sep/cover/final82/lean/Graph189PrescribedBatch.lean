import Graph189PrescribedClosure

open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Add any finite batch of edges whose degree sums are already at least n+1.
Deleting the batch preserves Hamilton paths with their original endpoints. -/
theorem prescribed_of_supergraph {G H : SimpleGraph V} [DecidableRel G.Adj] (incl : G ≤ H)
    (degree : ∀ a b, H.Adj a b → ¬G.Adj a b → Fintype.card V+1 ≤ G.degree a+G.degree b)
    {u v : V} (path : ∃ p : H.Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G≤J → J≤H → ∃ p : J.Walk u v, p.IsHamiltonian by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=H
    · subst J
      exact path
    have missing : ∃ a b, H.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,hab,hnot⟩ := missing
    have hEdge : edge a b ≤ H := by
      intro i j hij
      obtain ⟨h,_⟩ := (edge_adj a b i j).mp hij
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have key : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
      exact hnot (same.symm ▸ key)
    apply prescribed_of_sup_edge hab.ne hnot _ (ih _ strict (lower.trans le_sup_left) (sup_le upper hEdge))
    exact (degree _ _ hab (fun h => hnot (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v := a) lower) (degree_le_of_le (v := b) lower))

theorem complete_prescribed (u v : V) (hne : u ≠ v) :
    ∃ p : (⊤ : SimpleGraph V).Walk u v, p.IsHamiltonian := by
  classical
  let M := ((Finset.univ.erase u).erase v).toList
  let L := u :: (M ++ [v])
  have nd : L.Nodup := by
    simp [L,M,List.nodup_append',Finset.nodup_toList,hne]
  have chain : L.IsChain (⊤ : SimpleGraph V).Adj := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y A B eq
    apply (top_adj _ _).mpr
    intro same
    subst y
    rw [eq] at nd
    have tail := nd.of_append_right
    exact (List.nodup_cons.mp tail).1 (by simp)
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn chain
  have ps : p.support = L := Walk.support_ofSupport hn chain
  have ph : p.IsHamiltonian := (Walk.IsPath.mk' (by rwa [ps])).isHamiltonian_of_mem (by
    intro z
    rw [ps]
    by_cases hzu : z=u
    · simp [L,hzu]
    by_cases hzv : z=v <;> simp [L,M,hzu,hzv])
  have hs : L.head hn = u := by simp [L]
  have he : L.getLast hn = v := by simp [L]
  exact ⟨p.copy hs he, fun z => by simpa [Walk.support_copy] using ph z⟩

#print axioms complete_prescribed
#print axioms prescribed_of_supergraph
end Graph189TerminalLeafClosure
