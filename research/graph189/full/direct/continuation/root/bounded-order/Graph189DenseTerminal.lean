import Graph189SmallExteriorTransfer

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap Graph189OrdinaryPathGap Graph189RootedSplice
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exchange a tight gap with the whole clique. The new longest path has at
most k−1 omitted vertices. Its common contacts make every high vertex of the
exchanged gap visible at distance two, contradicting the original metric cap. -/
theorem no_dense_component {a b : V} {p : G.Walk a b} {C : Finset V}
    (h : Chosen p C G.secondSmallestDegree)
    (dense : ∀v∈C,G.secondSmallestDegree≤G.degree v → C.card+1≤2*(G.neighborFinset v∩C).card)
    (lo : 7≤G.secondSmallestDegree) (upper : Fintype.card V≤5*G.secondSmallestDegree-5)
    (conn : 3≤G.vertexConnectivity)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤G.secondSmallestDegree)
    (minimum : ∀v,3≤G.degree v)
    (uniqueLow : ∀u v,G.degree u<G.secondSmallestDegree → G.degree v<G.secondSmallestDegree → u=v)
    (gap : p.support.length+(G.secondSmallestDegree+1)/2+1<Fintype.card V) : False := by
  classical
  let k := G.secondSmallestDegree
  let m := C.card
  let s := k+1-m
  have sat := dense_clique h dense lo upper conn quota minimum uniqueLow gap
  have small := sat.small
  change m+2≤k at small
  have sum : m+s=k+1 := by dsimp [s]; omega
  have three : 3≤s := by omega
  obtain ⟨x,xc,xh⟩ := h.high
  have capx := xh.trans (internal_half h xc xh (quota _) minimum uniqueLow)
  have qsmall := card_le_card (inter_subset_right (s₁:=G.neighborFinset x) (s₂:=C))
  change _≤m at qsmall
  change 7≤k at lo
  have wideM : 4≤m := by change k≤_ at capx; omega
  obtain ⟨⟨y,yo,xy,yh⟩,_⟩ := high_exterior_half p h.path h.longest (h.outside _ xc) (quota _) xh minimum uniqueLow
  have yc := h.closed _ xc _ xy yo
  let u : C := ⟨x,xc⟩
  let v : C := ⟨y,yc⟩
  have ne : u≠v := fun eq => xy.ne (congrArg Subtype.val eq)
  have routes (i j : C) (diff : i≠j) : ∃q : (G.induce (C : Set V)).Walk i j,q.IsHamiltonian := by
    have full : G.induce (C : Set V) = ⊤ := by
      ext w z
      change G.Adj w.val z.val ↔ w≠z
      exact ⟨fun e eq => e.ne (congrArg Subtype.val eq), fun miss => sat.clique w.property z.property
        (fun eq => miss (Subtype.ext eq))⟩
    rw [full]; exact Graph189TerminalLeafClosure.complete_prescribed i j diff
  have uniform (z : V) (on : z∈p.support) (edge : G.Adj z u.val) : G.Adj z v.val :=
    sat.transfer xc yc yh on edge
  obtain ⟨A,count,rows,_⟩ := sat.marks
  have equality : contactPositions p x=A.map Fin.valEmbedding := by
    ext i
    constructor
    · intro hit
      obtain ⟨valid,e⟩ := (mem_contactPositions p x i).mp hit
      let j : Fin p.support.length := ⟨i,valid⟩
      exact mem_map.mpr ⟨j,(rows _ xc xh j).mp (by simpa only [get_at] using e),rfl⟩
    intro hit
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hit
    apply (mem_contactPositions p x _).mpr
    refine ⟨j.isLt,?_⟩
    change G.Adj (p.getVert j.val) x
    simpa only [get_at] using (rows _ xc xh j).mpr hj
  have marks : (contactPositions p u.val).card=s := by change (contactPositions p x).card=s; rw [equality,card_map]; exact count
  have Ptotal := card_outside_add_path p h.path C h.outside
  have room : p.support.length≤(s+1)*m+2*s := by
    change m+p.support.length≤Fintype.card V at Ptotal
    change Fintype.card V≤5*k-5 at upper
    have prod := Int.mul_nonneg (show 0≤(s:ℤ)-3 by omega) (show 0≤(m:ℤ)-3 by omega)
    zify at sum Ptotal ⊢
    have ub : (Fintype.card V:ℤ)≤5*(k:ℤ)-5 := by omega
    nlinarith only [prod,Ptotal,sum,ub]
  obtain ⟨l,t,width,bound,g,coords⟩ := find_tight_interval p h.path h.longest C m s rfl
    (by omega) (by omega) h.outside u v ne routes uniform marks room
  obtain ⟨root,rb,fromX,i,ig,edge⟩ := g.boundary
  have rootOn : root∈p.support := by rw [g.split]; simp only [List.mem_append] at rb ⊢; tauto
  have nd := h.path.support_nodup
  rw [g.split] at nd
  have rootOut : root∉g.block := by
    intro hit
    rcases List.mem_append.mp rb with left|right
    · exact List.disjoint_left.mp nd.of_append_left.disjoint left hit
    · exact List.disjoint_left.mp nd.disjoint (List.mem_append_right _ hit) right
  obtain ⟨c,d,Q,hQ,_,lengthQ,omits,stays⟩ := full_exterior_splice p h.path root rootOn C m rfl h.outside
    u v ne routes uniform g.left g.block g.right g.split rootOut g.before g.after
  have same : Q.support.length=p.support.length := by have := g.size; omega
  have lengths : Q.length=p.length := by have := Q.length_support; have := p.length_support; omega
  have longestQ : ∀{i j},∀q : G.Walk i j,q.IsPath → q.length≤Q.length :=
    fun q hq => (h.longest q hq).trans_eq lengths.symm
  have smallQ : Q.support.toFinsetᶜ.card+1≤k := by
    have sizeP := card_add_card_compl p.support.toFinset
    have sizeQ := card_add_card_compl Q.support.toFinset
    rw [List.toFinset_card_of_nodup h.path.support_nodup] at sizeP
    rw [List.toFinset_card_of_nodup hQ.support_nodup,same] at sizeQ
    have spare := sat.spare
    change _≤m+1 at spare
    omega
  have linked : ∃z,z∉Q.support ∧ G.Adj i z := by
    obtain ⟨j,lower,upper,eq⟩ := (segment_member p bound i).mp (coords ▸ ig)
    have pl := p.length_support
    have mem (q : ℕ) (low : l≤q) (high : q<t) : p.getVert q∈g.block :=
      coords.symm ▸ (segment_member p bound _).mpr ⟨q,low,high,rfl⟩
    by_cases start : j=l
    · exact ⟨p.getVert (j+1),omits _ (mem _ (by omega) (by omega)),eq ▸ p.adj_getVert_succ (i:=j) (by omega)⟩
    have adj := (p.adj_getVert_succ (i:=j-1) (by omega)).symm
    rw [show j-1+1=j by omega] at adj
    exact ⟨p.getVert (j-1),omits _ (mem _ (by omega) (by omega)),eq ▸ adj⟩
  have hits (w : V) (hw : w∈g.block) (high : G.secondSmallestDegree≤G.degree w) : G.dist u.val w=2 := by
    have on : w∈p.support := by simp [g.split,hw]
    have diff : u.val≠w := fun e => h.outside _ u.property (e ▸ on)
    have e := small_exterior_transfer hQ longestQ smallQ (omits _ ig) (omits _ hw) high linked
      (stays _ rb) edge lo upper conn quota minimum uniqueLow (same ▸ gap)
    exact two_step_metric diff (g.unmarked w hw) fromX e.symm
  have wide (i) (ii : i∈contactPositions p u.val) (j) (jj : j∈contactPositions p u.val) (lt : i<j) : i+3≤j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions p _ _).mp ii
    obtain ⟨jr,jc⟩ := (mem_contactPositions p _ _).mp jj
    have right := uniform (p.getVert j) (p.getVert_mem_support _) jc
    exact adjacent_omitted_contact_spacing p h.path h.longest (h.outside _ xc) (h.outside _ yc) xy
      ⟨i,ir⟩ ⟨j,jr⟩ lt (by simpa [get_at] using ic) (by simpa [get_at] using right)
  have debit := tight_gap_debit p h.path h.longest (h.outside _ u.property) (by omega : 3≤m)
    width bound marks wide g coords hits (quota _)
  change 2*s+m≤k+3 at debit
  omega

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.no_dense_component
