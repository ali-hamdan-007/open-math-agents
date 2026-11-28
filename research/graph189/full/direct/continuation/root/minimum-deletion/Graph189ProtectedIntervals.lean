import Graph189ExteriorGap

open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}

/-- A disjoint replacement comes with its complete support. This permits
maximization among paths that must retain a prescribed vertex. -/
theorem splice_support (p : G.Walk x y) (hp : p.IsPath)
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

private theorem kept_gap (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (kept : p.support[t.val] ∈ A ∨ p.support[t.val] ∈ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_support p hp A J B split q hq disjoint left right
  have member : p.support[t.val] ∈ r.support := by
    rw [rs]
    rcases kept with h | h <;> simp [h]
  have cmp := longest r hr member
  have pr := p.length_support
  have qr := r.length_support
  rw [split] at pr
  rw [rs] at qr
  simp only [List.length_append] at pr qr
  omega

private theorem mem_kept_suffix {L : List V} {t i : Fin L.length} (hi : i ≤ t) :
    L[t.val] ∈ L.drop i.val := by
  apply List.mem_drop_iff_getElem.mpr
  have le : i.val ≤ t.val := hi
  exact ⟨t.val-i.val,by have := t.isLt; omega,by simp [Nat.add_sub_of_le le]⟩

private theorem mem_kept_prefix {L : List V} {t i : Fin L.length} (hi : t ≤ i) :
    L[t.val] ∈ L.take (i.val+1) := by
  apply List.mem_take_iff_getElem.mpr
  exact ⟨t.val,lt_min (by change t.val ≤ i.val at hi; omega) t.isLt,rfl⟩

/-- An exterior detour ending at the first specified mark replaces the preceding prefix. -/
theorem protected_prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (hi : i ≤ t) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := kept_gap p hp t longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (Or.inr (mem_kept_suffix hi)) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega

/-- An exterior detour starting at the last specified mark replaces the following suffix. -/
theorem protected_suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (ht : t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := kept_gap p hp t longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (Or.inl (mem_kept_prefix ht)) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have ilt := i.isLt
  omega

/-- Every pair of distinct marked positions bounds a gap able to absorb a disjoint detour. -/
theorem protected_interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i<j) (ht : j ≤ t ∨ t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
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
  have bound := kept_gap p hp t longest _ _ _ split (ht.elim (fun h => Or.inr (mem_kept_suffix h))
    (fun h => Or.inl (mem_kept_prefix h))) q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega

#print axioms protected_interval_of_detour
#print axioms protected_prefix_of_detour
#print axioms protected_suffix_of_detour
end Graph189ExteriorGap
