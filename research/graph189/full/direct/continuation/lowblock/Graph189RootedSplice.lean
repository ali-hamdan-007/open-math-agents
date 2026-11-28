import Graph189ContactColumns

namespace Graph189RootedSplice
open SimpleGraph Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}

/-- Replace a contiguous segment by a vertex-disjoint detour, preserving the exact ordered support. -/
theorem splice_path (p : G.Walk x y) (hp : p.IsPath)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.support = A ++ q.support ++ B := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  exact ⟨_,_,r,Walk.IsPath.mk' (by rwa [rs]),rs⟩

/-- A longer detour through a longest path containing a designated root must discard that root. -/
theorem rooted_gap (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root ∈ p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length ∨ root ∈ J := by
  classical
  obtain ⟨u,v,r,hr,rs⟩ := splice_path p hp A J B split q hq disjoint left right
  by_cases kept : root∈J
  · exact Or.inr kept
  · have member : root∈r.support := by
      rw [rs]
      rw [split] at on
      simp only [List.mem_append] at on ⊢
      tauto
    have max := longest r hr member
    have lhs := r.length_support
    have rhs := p.length_support
    rw [rs] at lhs
    rw [split] at rhs
    simp only [List.length_append] at lhs rhs
    exact Or.inl (by omega)

theorem rooted_interval (p : G.Walk x y) (hp : p.IsPath)
    {root : V} (on : root∈p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i<j) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val ∨
      root ∈ (p.support.drop (i.val+1)).take (j.val-(i.val+1)) := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := rooted_gap p hp on longest _ _ _ split q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  rcases bound with yes|no
  · exact Or.inl (by omega)
  · exact Or.inr no


/-- Path vertices flanking an omitted neighbor are present because inserting at an endpoint always keeps the root. -/
theorem rooted_contact_internal (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root ∈ p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {a : V} (off : a∉p.support) (i : ℕ) (ri : i<p.support.length) (edge : G.Adj (p.getVert i) a) :
    0 < i ∧ i+1 < p.support.length := by
  classical
  have ext (A B : List V) (split : p.support=A++[]++B)
      (lc : ∀ z∈A.getLast?, G.Adj z a) (rc : ∀ z∈B.head?, G.Adj a z) : False := by
    have s := rooted_gap p hp on longest A [] B split (Walk.nil : G.Walk a a) (by simp)
      (by simpa [List.disjoint_left] using off) lc rc
    simp at s
  constructor
  · by_contra! bad
    obtain rfl : i=0 := by omega
    apply ext [] p.support (by simp) (by simp)
    intro z hz
    rw [List.head?_eq_some_head p.support_ne_nil,p.head_support] at hz
    have eq : x=z := by simpa using hz
    simpa [←eq] using edge.symm
  · by_contra! bad
    have il : i=p.length := by have := p.length_support; omega
    apply ext p.support [] (by simp) ?_ (by simp)
    intro z hz
    rw [List.getLast?_eq_some_getLast p.support_ne_nil,p.getLast_support] at hz
    have eq : y=z := by simpa using hz
    simpa [il,←eq] using edge

/-- The single possible intervening vertex of a two-step violation is the distinguished root. -/
theorem rooted_short_detour (p : G.Walk x y) (hp : p.IsPath) {root : V} (on : root ∈ p.support)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → root∈r.support → r.length ≤ p.length)
    {i j : ℕ} (ri : i<p.support.length) (rj : j<p.support.length) (lt : i<j)
    (q : G.Walk a b) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (first : G.Adj (p.getVert i) a) (last : G.Adj b (p.getVert j)) :
    i+1+q.support.length ≤ j ∨ (i+2≤j ∧ (j=i+2 → root=p.getVert (i+1))) := by
  have h := rooted_interval p hp on longest ⟨i,ri⟩ ⟨j,rj⟩ lt q hq dis
    (by simpa [get_at] using first) (by simpa [get_at] using last)
  rcases h with yes|exception
  · exact Or.inl yes
  · change root ∈ (p.support.drop (i+1)).take (j-(i+1)) at exception
    have greater : i+2≤j := by
      by_contra! bad
      have zero : j-(i+1)=0 := by omega
      simp [zero] at exception
    refine Or.inr ⟨greater,?_⟩
    intro h
    have one : j-(i+1)=1 := by omega
    rw [one] at exception
    have valid : i+1 < p.support.length := by omega
    have take : (p.support.drop (i+1)).take 1=[p.support[i+1]] := by
      simpa [List.head?_drop, List.getElem?_eq_getElem valid] using (List.take_one (l:=p.support.drop (i+1)))
    simpa [take, get_at] using exception

#print axioms rooted_short_detour
#print axioms rooted_contact_internal
end Graph189RootedSplice
