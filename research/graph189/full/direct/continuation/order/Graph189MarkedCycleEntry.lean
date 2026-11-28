import Graph189TwoCutSingleton

open SimpleGraph Finset
namespace Graph189MarkedCycleEntry
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- From any prescribed start in a connected graph, walk to a nearest
vertex of the closed path, then traverse all its vertices exactly once. -/
theorem enter (hc : G.Connected) (z : V) {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (close : G.Adj b a) : ∃y, ∃q : G.Walk z y, q.IsPath ∧ p.support.length≤q.support.length := by
  classical
  let W := p.support.toFinset
  obtain ⟨v,vW,nearest⟩ := W.exists_min_image (G.dist z) ⟨a,List.mem_toFinset.mpr p.start_mem_support⟩
  obtain ⟨t,len⟩ := (hc z v).exists_walk_length_eq_dist
  have tp := t.isPath_of_length_eq_dist len
  have only {w : V} (wt : w∈t.support) (ww : w∈W) : w=v := by
    by_contra ne
    have positive : 0<(t.dropUntil w wt).length := Nat.pos_of_ne_zero (fun h =>
      ne (Walk.length_eq_zero_iff.mp h).eq)
    have lower := G.dist_le (t.takeUntil w wt)
    have cmp := nearest w ww
    have split := congrArg Walk.length (Walk.take_spec t wt)
    rw [Walk.length_append] at split
    omega
  let C := p.cons close
  have vC : v∈C.support := List.mem_cons_of_mem _ (List.mem_toFinset.mp vW)
  let R := C.rotate v vC
  have live : ¬R.Nil := by
    intro bad
    have zero := bad.length_eq_zero
    rw [show R=C.rotate v vC from rfl,C.length_rotate] at zero
    simp [C] at zero
  let r := R.tail.reverse
  have perm : r.support.Perm p.support := by
    rw [show r=R.tail.reverse from rfl,Walk.support_reverse]
    apply (List.reverse_perm _).trans
    rw [R.support_tail_of_not_nil live]
    exact (C.support_rotate v vC).perm
  have rp := Walk.IsPath.mk' (p:=r) (perm.nodup_iff.mpr hp.support_nodup)
  have noStart : v∉r.support.tail := by
    have h := rp.support_nodup
    rw [←r.cons_tail_support] at h
    exact (List.nodup_cons.mp h).1
  let q := t.append r
  refine ⟨_,q,Walk.IsPath.mk' ?_,?_⟩
  · rw [show q=t.append r from rfl,Walk.support_append]
    apply List.nodup_append.mpr
    refine ⟨tp.support_nodup,rp.support_nodup.tail,?_⟩
    intro x xt y yr hxy
    subst y
    have xW : x∈W := List.mem_toFinset.mpr (perm.mem_iff.mp (List.mem_of_mem_tail yr))
    exact noStart ((only xt xW) ▸ yr)
  · rw [show q=t.append r from rfl,Walk.support_append,List.length_append,List.length_tail,perm.length_eq]
    have := t.length_support
    omega

#print axioms enter
end Graph189MarkedCycleEntry
