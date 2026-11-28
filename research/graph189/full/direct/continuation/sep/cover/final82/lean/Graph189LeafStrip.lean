import Graph189LeafEndpoints

open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}

private theorem strip_oriented
    (p : (terminalLeaves G u v).Walk (.inr false) (.inr true)) (hp : p.IsHamiltonian) :
    ∃ q : G.Walk u v, q.IsHamiltonian := by
  have nonnil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have first : p.snd = .inl u := neighbor_of_leaf (p.adj_snd nonnil).symm
  have qnn : ¬p.tail.Nil := Walk.not_nil_of_ne (by rw [first]; simp)
  have last : p.tail.penultimate = .inl v := neighbor_of_leaf (p.tail.adj_penultimate qnn)
  let t := p.tail.dropLast
  have parts : (.inr false) :: (t.support ++ [.inr true]) = p.support := by
    rw [show t.support ++ [.inr true] = p.tail.support from Walk.support_dropLast_concat qnn]
    exact Walk.cons_support_tail nonnil
  have nd := hp.isPath.support_nodup
  rw [←parts] at nd
  have ndf := List.nodup_cons.mp nd
  have core : ∀ z∈t.support, ∃ w : V, z = Sum.inl w := by
    intro z hz
    cases z with
    | inl w => exact ⟨w,rfl⟩
    | inr l =>
      cases l
      · exact (ndf.1 (List.mem_append_left _ hz)).elim
      · exact (List.disjoint_left.mp ndf.2.disjoint hz (by simp)).elim
  let project : V ⊕ Bool → V := Sum.elim id (fun l => if l then v else u)
  let L := t.support.map project
  have hn : L ≠ [] := by simp [L, t.support_ne_nil]
  have chain : L.IsChain G.Adj := by
    apply (List.isChain_map project).2
    apply t.isChain_adj_support.imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact hab
  have nodup : L.Nodup := by
    apply List.Nodup.map_on _ ndf.2.of_append_left
    intro a ha b hb h
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact congrArg Sum.inl h
  have all (w : V) : w ∈ L := by
    have hw := hp.mem_support (.inl w)
    rw [←parts] at hw
    have hmem : Sum.inl w ∈ t.support := by simpa using hw
    exact List.mem_map.mpr ⟨.inl w,hmem,rfl⟩
  let q := Walk.ofSupport L hn chain
  have qs : q.support = L := Walk.support_ofSupport hn chain
  have qh : q.IsHamiltonian := (Walk.IsPath.mk' (by rwa [qs])).isHamiltonian_of_mem
    (fun w => by rw [qs]; exact all w)
  have hstart : L.head hn = u := by
    simp [L,List.head_map,t,project,first]
  have hfinish : L.getLast hn = v := by
    simp [L,List.getLast_map,t,project,last]
  exact ⟨q.copy hstart hfinish, fun w => by simpa [Walk.support_copy] using qh w⟩

theorem prescribed_of_leaf_traceable
    (path : ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨x,y,p,hp⟩ := path
  rcases hamiltonian_leaf_at_end p hp false with hx | hy
  · subst x
    rcases hamiltonian_leaf_at_end p hp true with hf | hy
    · simp at hf
    · subst y
      exact strip_oriented p hp
  · subst y
    rcases hamiltonian_leaf_at_end p hp true with hx | hf
    · subst x
      apply strip_oriented p.reverse
      intro w
      simpa using hp w
    · simp at hf


#print axioms prescribed_of_leaf_traceable
end Graph189TerminalLeafClosure
