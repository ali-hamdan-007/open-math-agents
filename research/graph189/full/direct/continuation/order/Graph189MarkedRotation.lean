import Graph189TwoCutSingleton

open SimpleGraph Finset
namespace Graph189MarkedRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/- The two path rearrangements below are from the port-rotation proof and the
R2 list rotation of @carl2sheriff, adapted there from R1 by @computerfreak97. -/
private lemma rot {c : List V} (hc : c.IsChain G.Adj ∧ ∀ a ∈ c.getLast?, ∀ b ∈ c.head?, G.Adj a b) {q : V} (hq : q ∈ c) :
    ∃ c' : List V, c'.Perm c ∧ c'.IsChain G.Adj ∧ c'.head? = some q := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hq
  refine ⟨(q :: B) ++ A, List.perm_append_comm, ?_, by simp⟩
  obtain ⟨hch, hcl⟩ := hc
  rw [List.isChain_append] at hch
  refine List.isChain_append.2 ⟨hch.2.1, hch.1, ?_⟩
  intro x hx y hy
  apply hcl
  · rw [List.getLast?_append]
    have : (q :: B).getLast? = some x := hx
    simp [this]
  · rw [List.head?_append, hy]
    rfl

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


private def pivots {a b : V} (p : G.Walk a b) : Finset V := by
  classical
  exact ((range p.length).filter (fun j => G.Adj a (p.getVert (j+1)))).image p.getVert

private theorem enough {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ q : G.Walk x y,q.IsPath → q.length≤p.length) :
    G.degree a≤(pivots p).card := by
  classical
  let N := G.neighborFinset a
  let idx (v : V) := p.support.idxOf v
  let pred (v : V) := p.getVert (idx v-1)
  have loc (v : V) (hv : v∈N) : 0<idx v ∧ idx v≤p.length ∧ p.getVert (idx v)=v := by
    have e := (G.mem_neighborFinset _ _).mp hv
    have valid : idx v<p.support.length := List.idxOf_lt_length_iff.mpr (by
      by_contra outside
      have bound := longest (p.cons e.symm) (Walk.IsPath.mk' (by simp [outside,hp.support_nodup]))
      simp at bound)
    have eq := (Graph189ExteriorGap.get_at p valid).symm.trans (List.getElem_idxOf valid)
    refine ⟨?_,by have h := p.length_support; omega,eq⟩
    by_contra! no
    rw [show idx v=0 by omega,Walk.getVert_zero] at eq
    exact e.ne eq
  have inj : Set.InjOn pred (N:Set V) := by
    intro x hx y hy eq
    obtain ⟨i,lo,a⟩ := loc x hx
    obtain ⟨j,hi,b⟩ := loc y hy
    have l := hp.getVert_injOn (show idx x-1≤p.length by omega) (show idx y-1≤p.length by omega) eq
    exact a.symm.trans ((congrArg p.getVert (show idx x=idx y by omega)).trans b)
  have inc : N.image pred⊆pivots p := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hw
    obtain ⟨i,lo,eq⟩ := loc v hv
    apply mem_image.mpr
    refine ⟨idx v-1,mem_filter.mpr ⟨mem_range.mpr (by omega),?_⟩,rfl⟩
    rw [show idx v-1+1=idx v by omega,eq]
    exact (G.mem_neighborFinset _ _).mp hv
  have count := card_le_card inc
  rw [card_image_of_injOn inj] at count
  exact count

/-- If the two ends of a path touch, a mark on the path can start a
path of the same length. The path may omit vertices of its graph. -/
private theorem open_mark {a b : V} (p : G.Walk a b) (hp : p.IsPath) (close : G.Adj b a)
    (P : Finset V) (meet : ∃x∈P,x∈p.support) :
    ∃x∈P, ∃y, ∃q : G.Walk x y,q.IsPath ∧ q.support.length=p.support.length := by
  obtain ⟨x,xP,seen⟩ := meet
  obtain ⟨l,perm,chain,head⟩ := rot (G:=G) ⟨p.isChain_adj_support,by
    intro u hu v hv
    have ub : u=b := by simpa using hu
    have va : v=a := by simpa using hv
    simpa only [ub,va] using close⟩ seen
  have ne : l≠[] := by rintro rfl; simp at head
  let q := Walk.ofSupport l ne chain
  have supp : q.support=l := Walk.support_ofSupport ne chain
  have hx : l.head ne=x := by simpa [List.head?_eq_some_head ne] using head
  refine ⟨_,hx.symm ▸ xP,_,q,Walk.IsPath.mk' (supp ▸ perm.nodup_iff.mpr hp.support_nodup),?_⟩
  rw [supp,perm.length_eq]

/-- Rotate either end of a longest path. A pivot available from both ends
closes a cycle that omits precisely that pivot from the original path. -/
theorem from_longest {a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → q.length≤p.length)
    (P : Finset V) {loss : ℕ} (near : Fintype.card V≤p.support.length+loss)
    (marks : loss+2≤P.card) (room : Fintype.card V<G.degree a+G.degree b+P.card) :
    ∃x∈P, ∃y, ∃q : G.Walk x y,q.IsPath ∧ Fintype.card V≤q.support.length+(loss+1) := by
  classical
  by_contra no
  have misses {x y : V} (s : G.Walk x y) (hs : s.IsPath)
      (len : p.support.length=s.support.length) : Disjoint (pivots s) P := by
    apply Finset.disjoint_left.mpr
    intro v hv vP
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hv
    obtain ⟨jr,e⟩ := mem_filter.mp hj
    have valid := mem_range.mp jr
    obtain ⟨r,hr,eq⟩ := jump s hs (le_rfl : j≤j) (by omega) e
    exact no ⟨_,vP,_,r,hr,by omega⟩
  have rev : p.support.length=p.reverse.support.length := by simp
  have c₁ := enough p hp longest
  have c₂ := enough p.reverse hp.reverse (fun q hq => by simpa using longest q hq)
  have meet : ¬ Disjoint (pivots p) (pivots p.reverse) := by
    intro dis
    have inc : pivots p∪pivots p.reverse⊆univ\P := by
      intro x hx
      apply mem_sdiff.mpr
      refine ⟨mem_univ _,?_⟩
      rcases mem_union.mp hx with h|h
      · exact Finset.disjoint_left.mp (misses p hp rfl) h
      · exact Finset.disjoint_left.mp (misses p.reverse hp.reverse rev) h
    have count := card_le_card inc
    rw [card_union_of_disjoint dis,card_sdiff_of_subset (subset_univ P),card_univ] at count
    have cap := card_le_univ P
    omega
  obtain ⟨v,left,right⟩ := Finset.not_disjoint_iff.mp meet
  obtain ⟨j,jh,jv⟩ := mem_image.mp left
  obtain ⟨i,ih,iv⟩ := mem_image.mp right
  obtain ⟨jr,first⟩ := mem_filter.mp jh
  obtain ⟨ir,last⟩ := mem_filter.mp ih
  rw [Walk.length_reverse] at ir
  have jl := mem_range.mp jr
  have il := mem_range.mp ir
  rw [Walk.getVert_reverse] at iv last
  have same : p.length-i=j := hp.getVert_injOn (by change p.length-i≤p.length; omega)
    (by change j≤p.length; omega) (iv.trans jv.symm)
  have step : 0<j := by omega
  rw [show p.length-(i+1)=j-1 by omega] at last
  obtain ⟨q,hq,cost⟩ := jump p hp.isPath (show j-1≤j by omega) (by omega) first
  have long : Fintype.card V≤q.support.length+(loss+1) := by omega
  have contact : ∃x∈P,x∈q.support := by
    by_contra! absent
    have dis : Disjoint P q.support.toFinset := Finset.disjoint_left.mpr
      (fun x hx hy => absent x hx (List.mem_toFinset.mp hy))
    have count := card_le_univ (P∪q.support.toFinset)
    rw [card_union_of_disjoint dis,List.toFinset_card_of_nodup hq.support_nodup] at count
    omega
  obtain ⟨x,xP,y,r,hr,sz⟩ := open_mark q hq last P contact
  exact no ⟨x,xP,y,r,hr,by omega⟩

/-- Through order 2d+1 two ports suffice for a path missing at most one
vertex, including when the side has a cut vertex. -/
theorem from_two_marks (P : Finset V) (marks : 2≤P.card) {d : ℕ}
    (minimum : ∀ v,d≤G.degree v) (order : Fintype.card V≤2*d+1) :
    ∃x∈P, ∃y, ∃q : G.Walk x y,q.IsPath ∧ Fintype.card V≤q.support.length+1 := by
  classical
  obtain ⟨a,b,p,hp⟩ := Graph189PortPath.of_degree minimum order
  have len := hp.length_support
  apply from_longest p hp.isPath (loss:=0) _ P (by omega) marks
  · have := minimum a
    have := minimum b
    omega
  · intro _ _ q hq
    have s := hq.support_nodup.length_le_card
    have x := p.length_support
    have y := q.length_support
    omega

#print axioms from_longest
#print axioms from_two_marks
end Graph189MarkedRotation
