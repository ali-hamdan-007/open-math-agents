import Graph189ContactColumns

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}

private theorem replace_position (p : G.Walk x y) (hp : p.IsPath) (A B : List V)
    (mid a : V) (split : p.support=A++mid::B) (outside : a∉p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj a z) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase mid) := by
  have nd := hp.support_nodup
  have chain := p.isChain_adj_support
  rw [split] at nd chain outside
  have ndA := nd.of_append_left
  have ndMB := nd.of_append_right
  have ndB := (List.nodup_cons.mp ndMB).2
  have midB := (List.nodup_cons.mp ndMB).1
  have midA : mid∉A := fun h => List.disjoint_left.mp nd.disjoint h (by simp)
  have aA : a∉A := fun h => outside (List.mem_append_left _ h)
  have aB : a∉B := fun h => outside (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  let L := A++a::B
  have fresh : L.Nodup := by
    refine List.Nodup.append ndA (List.nodup_cons.mpr ⟨aB,ndB⟩) ?_
    rw [List.disjoint_left]
    intro z hz hz'
    rcases List.mem_cons.mp hz' with rfl | inB
    · exact aA hz
    · exact List.disjoint_left.mp nd.disjoint hz (List.mem_cons_of_mem _ inB)
  have rightChain : (a::B).IsChain G.Adj := chain.right_of_append.of_cons.cons right
  have adjacent : L.IsChain G.Adj := by
    apply chain.left_of_append.append rightChain
    intro z hz w hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have hn : L≠[] := by simp [L]
  let q := Walk.ofSupport L hn adjacent
  have qs : q.support=L := Walk.support_ofSupport hn adjacent
  refine ⟨_,_,q,Walk.IsPath.mk' (by rwa [qs]),?_,?_⟩
  · have ql := q.length_support
    have pl := p.length_support
    rw [qs] at ql
    rw [split] at pl
    simp only [L,List.length_append,List.length_cons] at ql pl
    omega
  · ext z
    simp only [qs,split,L,List.mem_toFinset,Finset.mem_insert,Finset.mem_erase,List.mem_append,List.mem_cons]
    by_cases eq : z=mid
    · subst z
      simp [midA,midB]
    · simp [eq]
      tauto

/-- Replacing the middle vertex of two path contacts by an omitted vertex
preserves the maximum length and changes precisely one member of the support. -/
theorem swap_contact_midpoint (p : G.Walk x y) (hp : p.IsPath) {a : V} (outside : a∉p.support)
    (i : ℕ) (lastValid : i+2 < p.support.length)
    (left : G.Adj (p.getVert i) a) (right : G.Adj (p.getVert (i+2)) a) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase (p.getVert (i+1))) := by
  let L := p.support
  let A := L.take (i+1)
  let B := L.drop (i+2)
  have mid : i+1 < L.length := by dsimp [L]; omega
  have first : i < L.length := by dsimp [L]; omega
  have pl : L=A++L[i+1]::B := by
    change L=L.take (i+1)++L[i+1]::L.drop (i+2)
    rw [←List.drop_eq_getElem_cons mid,List.take_append_drop]
  have lastA : A.getLast?=some L[i] :=
    (congrArg List.getLast? (List.take_succ_eq_append_getElem first)).trans List.getLast?_concat
  have firstB : B.head?=some L[i+2] := by simp [B,List.head?_drop]
  have changed := replace_position p hp A B L[i+1] a pl outside (by
    intro z hz
    rw [lastA] at hz
    have eq : L[i]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using left)) (by
    intro z hz
    rw [firstB] at hz
    have eq : L[i+2]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using right.symm))
  simpa [L,get_at] using changed

#print axioms swap_contact_midpoint
end Graph189ExteriorGap
