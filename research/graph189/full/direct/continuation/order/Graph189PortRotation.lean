import Graph189TwoCutSingleton

open SimpleGraph Finset
namespace Graph189PortRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Start at position i, traverse the prefix backwards and jump to position
j+1. Precisely j−i vertices of the old path are lost. -/
private theorem jump {a b : V} (p : G.Walk a b) (hp : p.IsPath) {i j : ℕ}
    (order : i≤j) (valid : j+1≤p.length) (pivot : G.Adj a (p.getVert (j+1))) :
    ∃ q : G.Walk (p.getVert i) b, q.IsPath ∧ q.support.length+(j-i)=p.support.length := by
  let l := (p.take i).reverse
  let r := p.drop (j+1)
  have disj : List.Disjoint l.support r.support := by
    have nd := hp.support_nodup
    have nd' : (p.support.take (i+1)++p.support.drop (i+1)).Nodup := by simpa using nd
    apply List.disjoint_left.mpr
    intro v vl vr
    have hl : v∈p.support.take (i+1) := by simpa [l,Walk.support_take] using vl
    have hr : v∈p.support.drop (j+1) := by
      simpa [r,Walk.drop_support_eq_support_drop_min,Nat.min_eq_left valid] using vr
    exact List.disjoint_left.mp nd'.disjoint hl ((List.drop_sublist_drop_left _ (by omega : i+1≤j+1)).subset hr)
  obtain ⟨q,hq,qs⟩ := Graph189TwoCutSingleton.joined l (hp.take i).reverse r (hp.drop _) pivot disj
  refine ⟨q,hq,?_⟩
  rw [qs,List.length_append,Walk.length_support,Walk.length_support,Walk.length_support]
  have hl : l.length=i := by simp [l,Walk.take_length,Nat.min_eq_left (show i≤p.length by omega)]
  have hr : r.length=p.length-(j+1) := Walk.drop_length _ _
  omega

/-- When a longest path contains a port, its first endpoint degree and the
number of nonports bound the cost of obtaining a path starting at a port. -/
theorem from_longest {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (P : Finset V) (on : ∃ i≤p.length, p.getVert i∈P) {s : ℕ}
    (few : (univ\P).card<G.degree a+s) :
    ∃ u∈P, ∃ v, ∃ q : G.Walk u v, q.IsPath ∧ p.support.length≤q.support.length+s := by
  classical
  by_contra deny
  have impossible {i j : ℕ} (order : i≤j) (valid : j+1≤p.length)
      (adj : G.Adj a (p.getVert (j+1))) (px : p.getVert i∈P) (close : j-i≤s) : False := by
    obtain ⟨q,hq,eq⟩ := jump p hp order valid adj
    exact deny ⟨_,px,_,q,hq,by omega⟩
  let M := (range (p.length+1)).filter (fun i => p.getVert i∈P)
  obtain ⟨u,uv,up⟩ := on
  have present : M.Nonempty := ⟨u,mem_filter.mpr ⟨mem_range.mpr (by omega),up⟩⟩
  let t := M.max' present
  have tm : t∈M := max'_mem _ _
  have tp : p.getVert t∈P := (mem_filter.mp tm).2
  have tr : t≤p.length := by have := mem_range.mp (mem_filter.mp tm).1; omega
  have room : t+s<p.length := by
    by_contra! h
    have len : (p.take t).reverse.support.length=t+1 := by
      rw [Walk.length_support,Walk.length_reverse,Walk.take_length,Nat.min_eq_left tr]
    exact deny ⟨_,tp,a,(p.take t).reverse,(hp.take t).reverse,by rw [len,p.length_support]; omega⟩
  let N := G.neighborFinset a
  let idx (v : V) := p.support.idxOf v
  let pred (v : V) := p.getVert (idx v-1)
  let succ (h : ℕ) := p.getVert (t+1+h)
  have spec (v : V) (hv : v∈N) : 0 < idx v ∧ idx v≤p.length ∧ p.getVert (idx v)=v := by
    have edge := (G.mem_neighborFinset _ _).mp hv
    have h : v∈p.support := by
      by_contra absent
      have bound := longest (p.cons edge.symm) (Walk.IsPath.mk' (by simp [absent,hp.support_nodup]))
      simp at bound
    have valid : idx v<p.support.length := List.idxOf_lt_length_iff.mpr h
    have eq := (Graph189ExteriorGap.get_at p valid).symm.trans (List.getElem_idxOf valid)
    refine ⟨?_,by have h:=p.length_support; omega,eq⟩
    by_contra! zero
    rw [show idx v=0 by omega,Walk.getVert_zero] at eq
    exact edge.ne eq
  have first : Set.InjOn pred (N:Set V) := by
    intro v hv w hw eq
    obtain ⟨a,b,c⟩ := spec v hv
    obtain ⟨x,y,z⟩ := spec w hw
    have loc : idx v-1=idx w-1 := hp.getVert_injOn
      (by change idx v-1≤p.length; omega) (by change idx w-1≤p.length; omega) eq
    exact c.symm.trans ((congrArg p.getVert (show idx v=idx w by omega)).trans z)
  have last : Set.InjOn succ (range s:Set ℕ) := by
    intro i hi j hj eq
    have iS := mem_range.mp hi
    have jS := mem_range.mp hj
    have same : t+1+i=t+1+j := hp.getVert_injOn
      (by change t+1+i≤p.length; omega) (by change t+1+j≤p.length; omega) eq
    omega
  have adj (v : V) (hv : v∈N) : G.Adj a (p.getVert ((idx v-1)+1)) := by
    obtain ⟨pos,_,eq⟩ := spec v hv
    rw [show idx v-1+1=idx v by omega,eq]
    exact (G.mem_neighborFinset _ _).mp hv
  have split : Disjoint (N.image pred) ((range s).image succ) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,eq⟩ := mem_image.mp hy
    obtain ⟨pos,valid,_⟩ := spec v hv
    have js := mem_range.mp hj
    have same : t+1+j=idx v-1 := hp.getVert_injOn
      (by change t+1+j≤p.length; omega) (by change idx v-1≤p.length; omega) eq
    exact impossible (by omega : t ≤ idx v-1) (by omega) (adj v hv) tp (by omega)
  have inc : N.image pred∪(range s).image succ ⊆ univ\P := by
    intro x hx
    apply mem_sdiff.mpr
    refine ⟨mem_univ _,?_⟩
    intro xp
    rcases mem_union.mp hx with predx|succx
    · obtain ⟨v,hv,rfl⟩ := mem_image.mp predx
      obtain ⟨pos,valid,_⟩ := spec v hv
      exact impossible le_rfl (by omega : idx v-1+1≤p.length) (adj v hv) xp (by omega)
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp succx
      have js := mem_range.mp hj
      have inside : t+1+j∈M := mem_filter.mpr ⟨mem_range.mpr (by omega),xp⟩
      have cmp := le_max' M (t+1+j) inside
      change t+1+j≤t at cmp
      omega
  have cnt := card_le_card inc
  rw [card_union_of_disjoint split,card_image_of_injOn first,card_image_of_injOn last,card_range] at cnt
  change (G.neighborFinset a).card+s ≤ _ at cnt
  rw [G.card_neighborFinset_eq_degree] at cnt
  omega

#print axioms from_longest
end Graph189PortRotation
