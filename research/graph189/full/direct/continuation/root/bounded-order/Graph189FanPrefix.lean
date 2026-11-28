import Graph189FanLinkage

open SimpleGraph
namespace Graph189FanCycle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- A chord from the first to the last vertex of a path lets any other specified
vertex start a path to that last vertex containing the first vertex and all
its neighbours from the original path. -/
theorem prefix_route {L : List V} {x r a : V} (nd : L.Nodup) (ch : L.IsChain G.Adj)
    (start : L.head? = some x) (stop : L.getLast? = some r) (edge : G.Adj x r)
    (on : a ∈ L) (distinct : a ≠ r) :
    ∃ W : List V, W.Nodup ∧ W.IsChain G.Adj ∧ W.head? = some a ∧ W.getLast? = some r ∧
      (∀ v ∈ W, v ∈ L) ∧ x ∈ W ∧ ∀ v ∈ L, G.Adj x v → v ∈ W := by
  classical
  obtain ⟨I,T,rfl⟩ := List.append_of_mem on
  let P := I ++ [a]
  have split : P ++ T = I ++ a :: T := by simp [P]
  have pn : P ≠ [] := by simp [P]
  have tn : T ≠ [] := by
    rintro rfl
    exact distinct (by simpa using stop)
  have last : T.getLast? = some r := by simpa only [←split,List.getLast?_append_of_ne_nil P tn] using stop
  have first : P.head? = some x := by simpa only [←split,List.head?_append_of_ne_nil _ pn] using start
  obtain ⟨A,b,B,eq,xb,no⟩ := OMA.BondyK.exists_first (G.Adj x) T ⟨r,List.mem_of_getLast? last,edge⟩
  subst T
  let Q := b :: B
  have newLast : Q.getLast? = some r := by simpa only [List.getLast?_append_cons] using last
  have nd' : (P ++ (A ++ Q)).Nodup := split ▸ nd
  have ch' : (P ++ (A ++ Q)).IsChain G.Adj := split ▸ ch
  have dis : P.reverse.Disjoint Q := fun _ vp vq => nd'.disjoint (List.mem_reverse.mp vp) (List.mem_append_right _ vq)
  have newChain : (P.reverse ++ Q).IsChain G.Adj := by
    apply (OMA.BondyK.chain_rev ch'.left_of_append).append ch'.right_of_append.right_of_append
    intro v hv u hu
    have ev : x = v := Option.some.inj (first.symm.trans (by simpa only [List.getLast?_reverse] using (show P.reverse.getLast? = some v from hv)))
    have eu : b = u := Option.some.inj hu
    exact ev ▸ eu ▸ xb
  refine ⟨P.reverse ++ Q,(List.nodup_reverse.mpr nd'.of_append_left).append nd'.of_append_right.of_append_right dis,
    newChain,?_,?_,?_,?_,?_⟩
  · simp [P]
  · rw [List.getLast?_append_of_ne_nil _ (show Q ≠ [] by simp [Q])]
    exact newLast
  · intro v hv
    rw [←split]
    rcases List.mem_append.mp hv with hp|hq
    · exact List.mem_append_left _ (List.mem_reverse.mp hp)
    exact List.mem_append_right _ (List.mem_append_right _ hq)
  · exact List.mem_append_left _ (List.mem_reverse.mpr (List.mem_of_mem_head? first))
  · intro v hv e
    rw [←split] at hv
    rcases List.mem_append.mp hv with hp|h
    · exact List.mem_append_left _ (List.mem_reverse.mpr hp)
    rcases List.mem_append.mp h with ha|hq
    · exact (no v ha e).elim
    exact List.mem_append_right _ hq

end Graph189FanCycle
#print axioms Graph189FanCycle.prefix_route
