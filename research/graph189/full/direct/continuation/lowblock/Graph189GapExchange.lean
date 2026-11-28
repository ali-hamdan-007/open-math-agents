import Graph189ProtectedSwap
import Graph189ContactColumns

open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}

/-- Replacing a real open interval by a spanning exterior route makes every
removed vertex adjacent to one old bounding mark, using the common-neighbor
property on the new maximal path. -/
theorem interval_exchange_witnesses_with_route (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo<hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val<lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0<lo ∨ hi<p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  let L := p.support
  let A := L.take lo
  let J := (L.drop lo).take (hi-lo)
  let B := L.drop hi
  have split : p.support=A++J++B := by
    change L=L.take lo++(L.drop lo).take (hi-lo)++L.drop hi
    rw [←List.take_add, Nat.add_sub_of_le nonempty.le,List.take_append_drop]
  have kept (i : Fin L.length) (s : i.val<lo ∨ hi ≤ i.val) : L[i.val]∈A ∨ L[i.val]∈B := by
    rcases s with u|v
    · exact Or.inl (List.mem_take_iff_getElem.mpr ⟨i.val,lt_min u i.isLt,rfl⟩)
    · exact Or.inr (List.mem_drop_iff_getElem.mpr
        ⟨i.val-hi,by have := i.isLt; omega,by simp [Nat.add_sub_of_le v]⟩)
  have inside (i : ℕ) (u : lo ≤ i) (v : i<hi) : p.getVert i ∈ J := by
    have ri : i<L.length := v.trans_le bound
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i-lo,?_,?_⟩
    · rw [List.length_drop]
      exact lt_min (Nat.sub_lt_sub_right u v) (Nat.sub_lt_sub_right u ri)
    · simpa only [List.getElem_drop, Nat.add_sub_of_le u] using get_at p ri
  have left : ∀ v∈A.getLast?, G.Adj v x := by
    intro v hv
    rcases lower with h | ⟨i,mem,e⟩
    · simp [A,h] at hv
    · have last : A.getLast? = some L[i.val] := by
        change (L.take lo).getLast? = _
        rw [←e]
        exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
          (l:=L) (i:=i.val) i.isLt)).trans List.getLast?_concat
      have same : L[i.val]=v := by simpa [last] using hv
      exact same ▸ (touch i mem).1
  have right : ∀ v∈B.head?, G.Adj y v := by
    intro v hv
    rcases upper with h | ⟨i,mem,e⟩
    · simp [B,L,h] at hv
    · have first : B.head?=some L[i.val] := by simp [B,←e,List.head?_drop]
      have same : L[i.val]=v := by simpa [first] using hv
      exact same ▸ (touch i mem).2.symm
  have length : q.support.length=J.length := by
    simp only [J,List.length_take,List.length_drop]
    rw [min_eq_left (Nat.sub_le_sub_right bound lo)]
    exact size.symm
  have witness : ∃ c, (c∈A ∨ c∈B) ∧ G.Adj x c ∧ ∃ v∈J, G.Adj c v := by
    rcases one with first|last
    · obtain zero | ⟨i,mem,e⟩ := lower
      · omega
      have edge := p.adj_getVert_succ (i:=i.val) (by have := p.length_support; omega)
      rw [e] at edge
      refine ⟨L[i.val],kept i (Or.inl (by omega)),(touch i mem).1.symm,
        p.getVert lo,inside lo le_rfl nonempty,?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt]
      exact edge
    · obtain tail | ⟨i,mem,e⟩ := upper
      · omega
      have edge := p.adj_getVert_succ (i:=hi-1) (by have := p.length_support; omega)
      rw [show hi-1+1=hi by omega] at edge
      refine ⟨L[i.val],kept i (Or.inr e.ge),(touch i mem).1.symm,
        p.getVert (hi-1),inside _ (by omega) (by omega),?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt,e]
      exact edge.symm
  obtain ⟨c,hc,cx,neighbor⟩ := witness
  have all := protected_swap_neighbors_with_route p hp _ A J B split (kept t safe) q hq dis length left right uniform hc neighbor
  intro i h
  exact ⟨c,cx,(all _ (inside i (mem_Ico.mp h).1 (mem_Ico.mp h).2)).symm⟩

theorem interval_exchange_witnesses (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo<hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val<lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0<lo ∨ hi<p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  apply interval_exchange_witnesses_with_route p hp t M q hq dis touch _ nonempty bound size safe lower upper one
  exact fun r hr hz _ => uniform r hr hz

#print axioms interval_exchange_witnesses
end Graph189ExteriorGap
