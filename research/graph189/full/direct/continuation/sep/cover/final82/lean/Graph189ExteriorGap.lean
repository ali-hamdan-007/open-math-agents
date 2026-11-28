import Graph189TraceClosurePublic

open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}

/-- Splicing a path outside a longest path, between consecutive marked positions
or from an end, forces the replaced interval to have at least as many vertices. -/
theorem gap_length_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
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
  have rlen := longest r (Walk.IsPath.mk' (by rwa [rs]))
  have lhs := r.length_support
  have rhs := p.length_support
  rw [rs] at lhs
  rw [split] at rhs
  simp only [L,List.length_append] at lhs rhs
  omega

#print axioms gap_length_of_detour
end Graph189ExteriorGap
