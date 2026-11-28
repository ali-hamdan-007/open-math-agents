import Graph189SixCycleSpanning
import Graph189QuadraticOrder

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189SixCycleExtra
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem cycle_card {r : V} (C : G.Walk r r) (hc : C.IsCycle) : C.support.toFinset.card=C.length := by
  have endmem : r∈C.support.tail := by
    rw [←C.support_tail_of_not_nil hc.not_nil]
    exact C.tail.end_mem_support
  have same : C.support.toFinset=C.support.tail.toFinset := by
    ext v
    simp only [List.mem_toFinset]
    constructor
    · intro h
      rw [←C.cons_tail_support] at h
      exact (List.mem_cons.mp h).elim (fun e => e ▸ endmem) id
    · exact List.mem_of_mem_tail
  rw [same,List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support]
  omega

theorem extends {r a b w : V} (C : G.Walk r r) (hc : C.IsCycle) (edge : s(a,b)∈C.edges)
    (outside : w∉C.support) (wa : G.Adj w a) (wb : G.Adj w b) :
    ∃ T : G.Walk w w, T.IsCycle ∧ T.length=C.length+1 ∧ ∀ v∈T.support, v=w ∨ v∈C.support := by
  obtain ⟨q,hq,len,sub⟩ := Graph189CycleEdgeMarks.complementary C hc edge
  let T := Walk.cons wa (q.concat wb.symm)
  have notOn : w∉q.support := fun h => outside (sub _ h)
  have Q := hq.concat notOn wb.symm
  have csize := hc.three_le_length
  have qlen := q.length_support
  have lengthT : T.length=C.length+1 := by simp [T]; omega
  refine ⟨T,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by omega⟩,lengthT,?_⟩
  · exact Q
  · intro v hv
    simp only [T,Walk.support_cons,Walk.support_concat,List.mem_cons,List.mem_append,List.mem_singleton] at hv
    exact hv.elim Or.inl (fun h => h.elim (fun hq => Or.inr (sub _ hq)) Or.inl)

variable [Fintype V] [Nontrivial V] [DecidableRel G.Adj]

/-- With seven omissions and one spanning six-cycle among them, every
vertex high, two distinct direct marks force a spanning exterior detour. -/
theorem seven {a b r : V} (p : G.Walk a b) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 2≤G.vertexConnectivity) (C : G.Walk r r) (hc : C.IsCycle) (six : C.length=6)
    (off : ∀ v∈C.support,v∉p.support) (size : p.support.toFinsetᶜ.card=7)
    (high : ∀ v, 6≤G.degree v) (order : Fintype.card V≤25)
    (has : ∀ w, w∉p.support → ∃ v, v∉p.support ∧ G.Adj w v) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let W := C.support.toFinset
  have inside : W⊆E := fun v hv => mem_compl.mpr fun h => off v (List.mem_toFinset.mp hv) (List.mem_toFinset.mp h)
  have wc : W.card=6 := (cycle_card C hc).trans six
  change E.card=7 at size
  obtain ⟨w,hw⟩ := card_pos.mp (show 0<(E\W).card by rw [card_sdiff_of_subset inside,size,wc]; decide)
  obtain ⟨wE,wW⟩ := mem_sdiff.mp hw
  have outsideW : w∉C.support := fun h => wW (List.mem_toFinset.mpr h)
  have wp : w∉p.support := fun h => (mem_compl.mp wE) (List.mem_toFinset.mpr h)
  have covers : insert w W=E := eq_of_subset_of_card_le (insert_subset wE inside)
    (by rw [card_insert_of_notMem wW,size,wc])
  obtain ⟨u,uo,wu⟩ := has w wp
  have uE : u∈E := mem_compl.mpr fun h => uo (List.mem_toFinset.mp h)
  have uW : u∈C.support := by
    rw [←covers,mem_insert] at uE
    exact List.mem_toFinset.mp (uE.resolve_left wu.ne.symm)
  let R := C.rotate u uW
  have rc : R.IsCycle := hc.rotate _
  have rl : R.length=6 := (C.length_rotate u _).trans six
  have inR (v : V) : v∈R.support ↔ v∈C.support := C.mem_support_rotate_iff u _
  have es : s(u,R.snd)∈R.edges := R.mk_start_snd_mem_edges rc.not_nil
  have ep : s(u,R.penultimate)∈R.edges := Sym2.eq_swap ▸ R.mk_penultimate_end_mem_edges rc.not_nil
  have absent {v : V} (uv : s(u,v)∈R.edges) : ¬G.Adj w v := by
    intro wv
    obtain ⟨T,hT,len,vertices⟩ := extends R rc uv (fun h => outsideW ((inR _).mp h)) wu wv
    have lower := Graph189TwoExteriorLinks.order_of_cycle p hp mx conn T hT (by
      intro z hz
      rcases vertices z hz with rfl|h
      · exact wp
      · exact off z ((inR _).mp h))
    omega
  have noS := absent es
  have noT := absent ep
  have sW := List.mem_toFinset.mpr ((inR _).mp (R.snd_mem_support_of_mem_edges es))
  have tW := List.mem_toFinset.mpr ((inR _).mp (R.snd_mem_support_of_mem_edges ep))
  have sE := inside sW
  have tE := inside tW
  have sw : R.snd≠w := fun e => wW (e ▸ sW)
  have tw : R.penultimate≠w := fun e => wW (e ▸ tW)
  have st := rc.snd_ne_penultimate
  have nbor {v u : V} (h : u∈G.neighborFinset v\p.support.toFinset) : u∈E :=
    mem_compl.mpr (mem_sdiff.mp h).2
  have wx : G.neighborFinset w\p.support.toFinset ⊆ ((E.erase w).erase R.snd).erase R.penultimate := by
    intro x hx
    have e := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1
    exact mem_erase.mpr ⟨fun eq => noT (eq ▸ e),mem_erase.mpr ⟨fun eq => noS (eq ▸ e),
      mem_erase.mpr ⟨e.ne.symm,nbor hx⟩⟩⟩
  have sx : G.neighborFinset R.snd\p.support.toFinset ⊆ (E.erase w).erase R.snd := by
    intro x hx
    have e := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1
    exact mem_erase.mpr ⟨e.ne.symm,mem_erase.mpr ⟨fun eq => noS (eq ▸ e).symm,nbor hx⟩⟩
  have wbound := card_le_card wx
  have sbound := card_le_card sx
  rw [card_erase_of_mem (mem_erase.mpr ⟨st.symm,mem_erase.mpr ⟨tw,tE⟩⟩),
    card_erase_of_mem (mem_erase.mpr ⟨sw,sE⟩),card_erase_of_mem wE,size] at wbound
  rw [card_erase_of_mem (mem_erase.mpr ⟨sw,sE⟩),card_erase_of_mem wE,size] at sbound
  have marks (v : V) : (G.neighborFinset v\p.support.toFinset).card+(contactPositions p v).card=G.degree v := by
    rw [contact_card_neighbors p hp,←G.card_neighborFinset_eq_degree]
    exact card_sdiff_add_card_inter _ _
  have swide := marks R.snd
  have wwide := marks w
  have ds := high R.snd
  have dw := high w
  obtain ⟨j,jm⟩ := card_pos.mp (show 0<(contactPositions p R.snd).card by omega)
  obtain ⟨i,im,diff⟩ := exists_mem_ne (show 1<(contactPositions p w).card by omega) j
  obtain ⟨li,ci⟩ := (mem_contactPositions _ _ _).mp im
  obtain ⟨lj,cj⟩ := (mem_contactPositions _ _ _).mp jm
  let I : Fin p.support.length := ⟨i,li⟩
  let K : Fin p.support.length := ⟨j,lj⟩
  have l : G.Adj p.support[I.val] w := by simpa only [I,get_at] using ci
  have r : G.Adj p.support[K.val] R.snd := by simpa only [K,get_at] using cj
  obtain ⟨q,hq,len,sub⟩ := Graph189CycleEdgeMarks.complementary R rc es
  let T := Walk.cons wu q
  have tp : T.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨hq,fun h => outsideW ((inR _).mp (sub _ h))⟩
  have dis : List.Disjoint T.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rcases List.mem_cons.mp hv with rfl|h
    · exact wp
    · exact off v ((inR _).mp (sub v h))
  have rev : List.Disjoint T.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have large : T.support.length=7 := by simp only [T,Walk.support_cons,List.length_cons,len,rl]
  have long {u v : V} (q : G.Walk u v) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
      (n : q.support.length=7) {f g : Fin p.support.length} (prior : f<g)
      (start : G.Adj p.support[f.val] u) (finish : G.Adj p.support[g.val] v) : 23≤p.support.length := by
    have backwards : List.Disjoint q.reverse.support p.support := by simpa [Walk.support_reverse] using dis
    have left := prefix_of_detour p hp mx f q.reverse hq.reverse backwards start.symm
    have mid := interval_of_detour p hp mx f g prior q hq dis start finish.symm
    have right := suffix_of_detour p hp mx g q.reverse hq.reverse backwards finish
    rw [Walk.support_reverse,List.length_reverse,n] at left right
    rw [n] at mid
    omega
  have ij : I≠K := fun eq => diff (congrArg Fin.val eq)
  have lower : 23≤p.support.length := by
    rcases lt_or_gt_of_ne ij with ik|ki
    · exact long T tp dis large ik l r
    · exact long T.reverse tp.reverse rev (by simpa using large) ki r l
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  omega

#print axioms seven
end Graph189SixCycleExtra
