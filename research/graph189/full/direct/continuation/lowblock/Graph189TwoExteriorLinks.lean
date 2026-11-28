import Graph189UpstreamBondy
import Graph189MatchedOrder
import Graph189MinimumCutOrder

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189TwoExteriorLinks
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}

/-- A trimmed link from an exterior set to a path, with the last edge
onto the path recorded separately. -/
structure Arm (p : G.Walk x y) (W : Finset V) where
  mark : Fin p.support.length
  root : V
  inside : root∈W
  port : V
  contact : G.Adj port p.support[mark.val]
  route : G.Walk root port
  simple : route.IsPath
  off : ∀ v∈route.support, v∉p.support
  away : ∀ v∈route.support.tail, v∉W

theorem arm_of_list (p : G.Walk x y) {W : Finset V}
    (apart : ∀ v∈W, v∉p.support) {l : List V}
    (h : OMA.BondyK.ABP G W p.support.toFinset l ∧
      (∀ v∈l.tail, v∉W) ∧ (∀ v∈l.dropLast,v∉p.support.toFinset)) :
    ∃ a : Arm p W, (∀ v∈a.route.support, v∈l) ∧ p.support[a.mark.val]∈l := by
  obtain ⟨⟨nd,ch,⟨r,hr,first⟩,⟨b,hb,last⟩⟩,tail,lastOff⟩ := h
  have ne : l≠[] := by intro e; simp [e] at first
  have split : l=l.dropLast++[b] := by
    rw [List.getLast?_eq_getLast_of_ne_nil ne,Option.some.injEq] at last
    rw [←last,List.dropLast_append_getLast]
  let M := l.dropLast
  have mne : M≠[] := by
    intro eq
    change l.dropLast=[] at eq
    rw [split,eq] at first
    simp only [List.nil_append,List.head?_cons,Option.some.injEq] at first
    exact apart r hr (first ▸ List.mem_toFinset.mp hb)
  have hd : M.head mne=r := by
    have e : l=M++[b] := split
    rw [e,List.head?_append,List.head?_eq_some_head mne] at first
    simpa using first
  have dc := nd
  have cc := ch
  change l=M++[b] at split
  rw [split] at dc cc
  have subch := (List.isChain_append.mp cc).1
  let q := Walk.ofSupport M mne subch
  have supp : q.support=M := Walk.support_ofSupport mne subch
  let j : Fin p.support.length := ⟨p.support.idxOf b,List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp hb)⟩
  have mark : p.support[j.val]=b := List.getElem_idxOf j.isLt
  have touch : G.Adj (M.getLast mne) p.support[j.val] := by
    rw [mark]
    exact (List.isChain_append.mp cc).2.2 _ (List.getLast?_eq_getLast_of_ne_nil mne) _ rfl
  let a : Arm p W := {
    mark := j
    root := M.head mne
    inside := hd ▸ hr
    port := M.getLast mne
    contact := touch
    route := q
    simple := Walk.IsPath.mk' (by rw [supp]; exact dc.of_append_left)
    off := by
      intro v hv hit
      rw [supp] at hv
      exact lastOff v hv (List.mem_toFinset.mpr hit)
    away := by
      intro v hv
      rw [supp] at hv
      apply tail
      rw [split,List.tail_append_of_ne_nil mne]
      exact List.mem_append_left _ hv }
  refine ⟨a,?_,?_⟩
  · intro v hv
    change v∈q.support at hv
    rw [supp] at hv
    rw [split]
    exact List.mem_append_left _ hv
  · change p.support[j.val]∈l
    rw [mark]
    exact List.mem_of_getLast? last

omit [DecidableEq V] in
private theorem Arm.start {p : G.Walk x y} {W : Finset V} (a : Arm p W)
    (outside : ∀ v∈W, v∉p.support) {b : V} (q : G.Walk a.root b) (hq : q.IsPath)
    (uses : ∀ v∈q.support, v∈W) :
    (a.route.reverse.append q).IsPath ∧
      ∀ v∈(a.route.reverse.append q).support, v∉p.support := by
  constructor
  · apply Walk.IsPath.mk'
    rw [Walk.support_append_eq_support_dropLast_append,Walk.support_reverse,List.dropLast_reverse]
    apply List.Nodup.append (by simpa using a.simple.support_nodup.tail) hq.support_nodup
    intro u hu hv
    exact a.away u (List.mem_reverse.mp hu) (uses u hv)
  · intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with ha|hb
    · exact a.off v (by simpa using ha)
    · exact outside v (uses v hb)

omit [DecidableEq V] in
theorem ordered_positions {p : G.Walk x y} (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    {W : Finset V} (outside : ∀ v∈W, v∉p.support)
    (a b : Arm p W) (before : a.mark<b.mark)
    (distinct : ∀ v∈a.route.support, v∉b.route.support) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m≤q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t≤q.support.length ∧ ∀ v∈q.support,v∈W) :
    m≤a.mark.val ∧ a.mark.val+1+t≤b.mark.val ∧ b.mark.val+1+m≤p.support.length := by
  obtain ⟨_,q1,h1,len1,W1⟩ := start a.root a.inside
  obtain ⟨h1',off1⟩ := a.start outside q1 h1 W1
  obtain ⟨_,q2,h2,len2,W2⟩ := start b.root b.inside
  obtain ⟨h2',off2⟩ := b.start outside q2 h2 W2
  have localDis {i j} (q : G.Walk i j) (h : ∀ v∈q.support,v∉p.support) :
      List.Disjoint q.support p.support := List.disjoint_left.mpr h
  have l := prefix_of_detour p hp longest a.mark (a.route.reverse.append q1).reverse h1'.reverse
    (by
      apply List.disjoint_left.mpr
      intro v hv
      rw [Walk.support_reverse,List.mem_reverse] at hv
      exact off1 v hv) a.contact
  have r := suffix_of_detour p hp longest b.mark _ h2' (localDis _ off2) b.contact.symm
  have diff : a.root≠b.root := by
    intro eq
    apply distinct _ a.route.start_mem_support
    rw [eq]
    exact b.route.start_mem_support
  obtain ⟨q,hq,len,mem⟩ := join a.root a.inside b.root b.inside diff
  obtain ⟨path,dis⟩ := a.start outside q hq mem
  let T := (a.route.reverse.append q).append b.route
  have pathT : T.IsPath := by
    apply Walk.IsPath.mk'
    rw [show T=(a.route.reverse.append q).append b.route from rfl,Walk.support_append]
    apply List.Nodup.append path.support_nodup b.simple.support_nodup.tail
    intro u hu hv
    rcases (Walk.mem_support_append_iff _ _).mp hu with ha|hh
    · exact distinct u (by simpa using ha) (List.mem_of_mem_tail hv)
    · exact b.away u hv (mem u hh)
  have disT : List.Disjoint T.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with h|h
    · exact dis v h
    · exact b.off v h
  have inner := interval_of_detour p hp longest a.mark b.mark before T pathT disT a.contact.symm b.contact
  have plen := p.length_support
  simp only [T,Walk.length_support,Walk.length_append,Walk.length_reverse] at l r inner len1 len2 len
  exact ⟨by omega,by omega,by omega⟩

/-- Extract any requested number of vertex-disjoint trimmed arms. -/
theorem arms [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (count : ℕ) (conn : count≤G.vertexConnectivity) (wide : count≤W.card) (longP : count≤p.support.length) :
    ∃ A : Fin count→Arm p W, Function.Injective (fun i => (A i).mark) ∧
      ∀ i j, i≠j → ∀ v∈(A i).route.support,v∉(A j).route.support := by
  classical
  let P := p.support.toFinset
  have szP : count≤P.card := by
    rw [show P=p.support.toFinset from rfl,List.toFinset_card_of_nodup hp.support_nodup]
    exact longP
  obtain ⟨L,hL,separate⟩ := OMA.BondyK.menger_trim (G:=G) W P count (by
    intro S separates
    by_contra! small
    have leftover (T : Finset V) (big : count≤T.card) : ∃ v∈T,v∉S := by
      by_contra! inc
      have := card_le_card (show T⊆S from inc)
      omega
    obtain ⟨r,hr,rS⟩ := leftover W wide
    obtain ⟨b,hb,bS⟩ := leftover P szP
    obtain ⟨q,hq⟩ := (Graph189CutSides.connected_after_smaller_deletion (G:=G) S (small.trans_le conn)).exists_isPath
      (⟨r,rS⟩ : {v : V | v∉S}) ⟨b,bS⟩
    obtain ⟨v,hv,vs⟩ := separates (q.support.map Subtype.val) ⟨hq.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr q.isChain_adj_support,
      ⟨r,hr,by rw [←q.cons_tail_support,List.map_cons,List.head?_cons]⟩,
      ⟨b,hb,by rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil q.support_ne_nil,q.getLast_support]; rfl⟩⟩
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact v.property vs)
  choose A included ends using fun i => arm_of_list p outside (hL i)
  refine ⟨A,?_,fun i j ne v hi hj => separate i j ne v (included i v hi) (included j v hj)⟩
  intro i j eq
  by_contra ne
  apply separate i j ne _ (ends i)
  change (A i).mark=(A j).mark at eq
  simpa only [eq] using ends j

/-- Two disjoint links force two exterior tails and a joining interval on the original longest path. -/
theorem path_of_routes [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (wide : 2≤W.card) (longP : 2≤p.support.length) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m≤q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t≤q.support.length ∧ ∀ v∈q.support,v∈W) :
    2*m+t+2≤p.support.length := by
  classical
  obtain ⟨A,inj,separate⟩ := arms p hp W outside 2 conn wide longP
  let a := A 0
  let b := A 1
  have dis := separate 0 1 (by decide)
  have diff : a.mark≠b.mark := fun eq => (show (0:Fin 2)≠1 by decide) (inj eq)
  rcases lt_or_gt_of_ne diff with ab|ba
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside a b ab dis start join
    omega
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside b a ba (fun v hb ha => dis v ha hb) start join
    omega

/-- In a two-connected graph, any exterior vertex set of a longest path
supports two disjoint links to that path. Spanning tails and prescribed
interior routes then give the indicated ambient-order bound. -/
theorem order_of_routes [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (wide : 2≤W.card) (longP : 2≤p.support.length) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m≤q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t≤q.support.length ∧ ∀ v∈q.support,v∈W) :
    W.card+2*m+t+2≤Fintype.card V := by
  have n := card_outside_add_path p hp W outside
  have l := path_of_routes p hp longest conn W outside wide longP start join
  omega

/-- An exterior cycle gives a spanning tail at every root and a rounded
half-cycle route between every pair of distinct terminals. -/
theorem cycle_routes {r : V} (C : G.Walk r r) (hc : C.IsCycle) :
    let W := C.support.toFinset
    C.length≤W.card ∧
    (∀ a∈W, ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length≤q.support.length ∧ ∀ v∈q.support,v∈W) ∧
    (∀ a∈W, ∀ b∈W, a≠b → ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1≤q.support.length ∧ ∀ v∈q.support,v∈W) := by
  classical
  let W := C.support.toFinset
  have width : C.length≤W.card := by
    have sub : C.support.tail.toFinset⊆W := by
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hv))
    have h := card_le_card sub
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support] at h
    omega
  have contains (a : V) (ha : a∈W) (v : V) (hv : v∈(C.rotate a (List.mem_toFinset.mp ha)).support) :
      v∈W := List.mem_toFinset.mpr ((C.mem_support_rotate_iff a _).mp hv)
  have start (a : V) (ha : a∈W) :
      ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length≤q.support.length ∧ ∀ v∈q.support, v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have l : R.length=C.length := C.length_rotate _ _
    have h := R.length_dropLast_add_one rc.not_nil
    refine ⟨_,R.dropLast,rc.isPath_dropLast,by rw [Walk.length_support]; omega,?_⟩
    intro v hv
    apply contains a ha
    rw [Walk.support_dropLast rc.not_nil] at hv
    exact List.dropLast_subset _ hv
  have pair (a : V) (ha : a∈W) (b : V) (hb : b∈W) (diff : a≠b) :
      ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1≤q.support.length ∧ ∀ v∈q.support,v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have on : b∈R.support := (C.mem_support_rotate_iff a _).mpr (List.mem_toFinset.mp hb)
    let L := R.takeUntil b on
    let T := R.dropUntil b on
    have split : L.append T=R := R.take_spec on
    have cycle : (L.append T).IsCycle := split ▸ rc
    have lp : L.IsPath := rc.isPath_takeUntil on
    have tp : T.IsPath := cycle.isPath_of_append_right (L.not_nil_of_ne diff)
    have lengths : L.length+T.length=C.length := by
      rw [←Walk.length_append,split]
      exact C.length_rotate _ _
    by_cases large : (C.length+1)/2≤L.length
    · exact ⟨L,lp,by rw [L.length_support]; omega,fun v hv =>
        contains a ha v (R.support_takeUntil_subset_support on hv)⟩
    · exact ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,fun v hv =>
        contains a ha v (R.support_dropUntil_subset_support on (by simpa using hv))⟩
  exact ⟨width,start,pair⟩

/-- The positions forced by two links to a cycle stay on the given path. -/
theorem path_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    2*C.length+(C.length+1)/2+3≤p.support.length := by
  classical
  let W := C.support.toFinset
  obtain ⟨width,start,pair⟩ := cycle_routes C hc
  change C.length≤W.card at width
  obtain ⟨_,q,hq,ql,_⟩ := start r (List.mem_toFinset.mpr C.start_mem_support)
  have mx := longest q hq
  have hq' := q.length_support
  have hp' := p.length_support
  have three := hc.three_le_length
  have ord := path_of_routes p hp longest conn W (fun v hv => outside v (List.mem_toFinset.mp hv))
    (by omega) (by omega) start pair
  omega

/-- The longer cycle arc gives a rounded half-length detour between the
two links, while either link can start a path traversing the whole cycle. -/
theorem order_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    3*C.length+(C.length+1)/2+3≤Fintype.card V := by
  classical
  have n := card_outside_add_path p hp C.support.toFinset (fun v hv => outside v (List.mem_toFinset.mp hv))
  have width := (cycle_routes C hc).1
  have l := path_of_cycle p hp longest conn C hc outside
  omega

end Graph189TwoExteriorLinks
#print axioms Graph189TwoExteriorLinks.order_of_routes
#print axioms Graph189TwoExteriorLinks.order_of_cycle
