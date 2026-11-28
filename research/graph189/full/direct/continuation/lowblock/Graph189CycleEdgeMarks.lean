import Graph189TwoExteriorLinks

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189CycleEdgeMarks
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Removing a specified cycle edge gives a path through the entire cycle
between the two endpoints of that edge. -/
theorem complementary {r a b : V} (C : G.Walk r r) (hc : C.IsCycle)
    (edge : s(a,b)∈C.edges) : ∃ q : G.Walk a b, q.IsPath ∧ q.support.length=C.length ∧
      ∀ v∈q.support,v∈C.support := by
  have ha := C.fst_mem_support_of_mem_edges edge
  have hb := C.snd_mem_support_of_mem_edges edge
  have diff := (C.adj_of_mem_edges edge).ne
  let R := C.rotate a ha
  have rc : R.IsCycle := hc.rotate _
  have bR : b∈R.support := (C.mem_support_rotate_iff a ha).mpr hb
  let L := R.takeUntil b bR
  let T := R.dropUntil b bR
  have split : L.append T=R := R.take_spec bR
  have lp : L.IsPath := rc.isPath_takeUntil bR
  have tp : T.IsPath := (show (L.append T).IsCycle from split ▸ rc).isPath_of_append_right
    (L.not_nil_of_ne diff)
  have lengths : L.length+T.length=C.length := by
    rw [← Walk.length_append,split]
    exact C.length_rotate a ha
  have edgeR : s(a,b)∈R.edges := (C.rotate_edges a ha).mem_iff.mpr edge
  rw [←split,Walk.edges_append,List.mem_append] at edgeR
  rcases edgeR with left|right
  · have one := lp.length_eq_one_of_mem_edges left
    refine ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,?_⟩
    intro v hv
    apply (C.mem_support_rotate_iff a ha).mp
    exact R.support_dropUntil_subset_support bR (by simpa using hv)
  · have e : s(b,a)∈T.edges := Sym2.eq_swap ▸ right
    have one := tp.length_eq_one_of_mem_edges e
    exact ⟨L,lp,by rw [Walk.length_support]; omega,fun v hv =>
      (C.mem_support_rotate_iff a ha).mp (R.support_takeUntil_subset_support bR hv)⟩

/-- Two path marks at the ends of a specified exterior cycle edge force
three gaps, each containing at least the order of the cycle. -/
theorem positions {x y r a b : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (off : ∀ v∈C.support,v∉p.support)
    (edge : s(a,b)∈C.edges) {i j : Fin p.support.length} (before : i<j)
    (left : G.Adj p.support[i.val] a) (right : G.Adj p.support[j.val] b) :
    C.length≤i.val ∧ i.val+1+C.length≤j.val ∧ j.val+1+C.length≤p.support.length := by
  obtain ⟨q,hq,len,sub⟩ := complementary C hc edge
  have dis : List.Disjoint q.support p.support := List.disjoint_left.mpr
    (fun v hv => off v (sub v hv))
  have rev : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have lo := prefix_of_detour p hp mx i q.reverse hq.reverse rev left.symm
  have mid := interval_of_detour p hp mx i j before q hq dis left right.symm
  have hi := suffix_of_detour p hp mx j q.reverse hq.reverse rev right
  rw [Walk.support_reverse,List.length_reverse,len] at lo hi
  rw [len] at mid
  exact ⟨lo,mid,hi⟩

#print axioms positions
end Graph189CycleEdgeMarks
