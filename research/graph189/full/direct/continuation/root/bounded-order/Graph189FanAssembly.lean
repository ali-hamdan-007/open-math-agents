import Graph189FanLinkage

open SimpleGraph
namespace Graph189FanLinkage

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

private theorem walk_of_chain {S : List V} {x y : V} (chain : S.IsChain G.Adj)
    (first : S.head? = some x) (last : S.getLast? = some y) :
    ∃ w : G.Walk x y, w.support = S := by
  have ne : S ≠ [] := by
    intro e
    simp [e] at first
  have hx : S.head ne = x := Option.some.inj ((List.head?_eq_some_head ne).symm.trans first)
  have hy : S.getLast ne = y := Option.some.inj ((List.getLast?_eq_some_getLast ne).symm.trans last)
  exact ⟨(Walk.ofSupport S ne chain).copy hx hy, by
    rw [Walk.support_copy, Walk.support_ofSupport]⟩

private theorem head_not_mem_tail {S : List V} {a : V} (nd : S.Nodup)
    (head : S.head? = some a) : a ∉ S.tail := by
  cases S with
  | nil => simp
  | cons x T =>
    have xa : x = a := Option.some.inj head
    subst x
    exact (List.nodup_cons.mp nd).1

/-- Join two routes, crossing between their terminal sets on two trimmed
links. The routes can share their last vertex when the second link is a
singleton. All other intersections must be at the specified ends. -/
theorem join_routes {a b c d : V} (L R U W : List V)
    (left : L.Nodup) (leftChain : L.IsChain G.Adj)
    (leftStart : L.head? = some a) (leftEnd : L.getLast? = some c)
    (leftIn : ∀ x ∈ L, x ∈ A)
    (right : R.Nodup) (rightChain : R.IsChain G.Adj)
    (rightStart : R.head? = some b) (rightEnd : R.getLast? = some d)
    (rightIn : ∀ x ∈ R, x ∈ B)
    (meet : ∀ x ∈ L, x ∈ R → x = d)
    (first : Link G A B U) (second : Link G A B W) (apart : U.Disjoint W)
    (firstStart : U.head? = some a) (firstEnd : U.getLast? = some b)
    (secondStart : W.head? = some c) (secondEnd : W.getLast? = some d)
    (long : 3 ≤ (L.length - 1) + (R.length - 1) + (U.length - 1) + (W.length - 1)) :
    ∃ cycle : G.Walk a a, cycle.IsCycle ∧
      (∀ x, x ∈ L ∨ x ∈ R → x ∈ cycle.support) ∧
      cycle.length + 4 = L.length + R.length + U.length + W.length := by
  obtain ⟨l, hl⟩ := walk_of_chain leftChain leftStart leftEnd
  obtain ⟨r, hr⟩ := walk_of_chain rightChain rightStart rightEnd
  obtain ⟨u, hu⟩ := walk_of_chain first.chain firstStart firstEnd
  obtain ⟨w, hw⟩ := walk_of_chain second.chain secondStart secondEnd
  let cycle := l.append (w.append (r.reverse.append u.reverse))
  have length : cycle.length = l.length + w.length + r.length + u.length := by
    simp only [cycle, Walk.length_append, Walk.length_reverse]
    omega
  have ll := l.length_support
  have lr := r.length_support
  have lu := u.length_support
  have lw := w.length_support
  rw [hl] at ll
  rw [hr] at lr
  rw [hu] at lu
  rw [hw] at lw
  have enough : 3 ≤ cycle.length := by omega
  have revRight := List.nodup_reverse.mpr right
  have revFirst := List.nodup_reverse.mpr first.nodup
  have dOff : d ∉ R.reverse.tail := head_not_mem_tail revRight (by simpa using rightEnd)
  have bOff : b ∉ U.reverse.tail := head_not_mem_tail revFirst (by simpa using firstEnd)
  have aOff : a ∉ L.tail := head_not_mem_tail left leftStart
  have cOff : c ∉ W.tail := head_not_mem_tail second.nodup secondStart
  have lwDis : L.tail.Disjoint W.tail := by
    intro x xl xw
    have only := second.onlyA x (List.mem_of_mem_tail xw) (leftIn x (List.mem_of_mem_tail xl))
    have eq : x = c := Option.some.inj (only.symm.trans secondStart)
    exact cOff (eq ▸ xw)
  have lrDis : L.tail.Disjoint R.reverse.tail := by
    intro x xl xr
    have eq := meet x (List.mem_of_mem_tail xl) (List.mem_reverse.mp (List.mem_of_mem_tail xr))
    exact dOff (eq ▸ xr)
  have luDis : L.tail.Disjoint U.reverse.tail := by
    intro x xl xu
    have only := first.onlyA x (List.mem_reverse.mp (List.mem_of_mem_tail xu))
      (leftIn x (List.mem_of_mem_tail xl))
    have eq : x = a := Option.some.inj (only.symm.trans firstStart)
    exact aOff (eq ▸ xl)
  have wrDis : W.tail.Disjoint R.reverse.tail := by
    intro x xw xr
    have only := second.onlyB x (List.mem_of_mem_tail xw)
      (rightIn x (List.mem_reverse.mp (List.mem_of_mem_tail xr)))
    have eq : x = d := Option.some.inj (only.symm.trans secondEnd)
    exact dOff (eq ▸ xr)
  have wuDis : W.tail.Disjoint U.reverse.tail := by
    intro x xw xu
    exact apart (List.mem_reverse.mp (List.mem_of_mem_tail xu)) (List.mem_of_mem_tail xw)
  have ruDis : R.reverse.tail.Disjoint U.reverse.tail := by
    intro x xr xu
    have only := first.onlyB x (List.mem_reverse.mp (List.mem_of_mem_tail xu))
      (rightIn x (List.mem_reverse.mp (List.mem_of_mem_tail xr)))
    have eq : x = b := Option.some.inj (only.symm.trans firstEnd)
    exact bOff (eq ▸ xu)
  have isCycle : cycle.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨Walk.IsPath.mk' ?_, enough⟩
    rw [cycle.support_tail_of_not_nil (fun h => by have := h.length_eq_zero; omega)]
    simp only [cycle, Walk.tail_support_append, Walk.support_reverse, hl, hr, hu, hw]
    refine left.tail.append (second.nodup.tail.append (revRight.tail.append revFirst.tail ruDis) ?_) ?_
    · intro x inW inRest
      exact (List.mem_append.mp inRest).elim (wrDis inW) (wuDis inW)
    · intro x inL inRest
      rcases List.mem_append.mp inRest with inW | inRest
      · exact lwDis inL inW
      exact (List.mem_append.mp inRest).elim (lrDis inL) (luDis inL)
  refine ⟨cycle, isCycle, ?_, by omega⟩
  intro x hx
  rw [show cycle = l.append (w.append (r.reverse.append u.reverse)) from rfl]
  simp only [Walk.mem_support_append_iff, Walk.support_reverse, List.mem_reverse, hl, hr]
  exact hx.elim Or.inl (fun h => Or.inr (Or.inr (Or.inl h)))

end Graph189FanLinkage

#print axioms Graph189FanLinkage.join_routes
