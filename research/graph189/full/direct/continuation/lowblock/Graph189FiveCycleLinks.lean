import Graph189FiveCycleRing

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189FiveCycleLinks
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- A route between two distinct vertices outside an extremal five-cycle
cannot use two distinct anchors on the cycle. The longer arc and the
route between the anchors would form a cycle of length at least six. -/
theorem same_anchor {a b r : V} (p : G.Walk a b) (C : G.Walk r r) (hc : C.IsCycle)
    (five : C.length=5) (off : ∀v∈C.support,v∉p.support)
    (bound : ∀ {v}, ∀ T : G.Walk v v, T.IsCycle → (∀ w∈T.support,w∉p.support) → T.length≤5)
    (F : Finset V) (away : ∀ v∈F, v∉p.support ∧ v∉C.support)
    {x y : F} (xy : x≠y) (reach : (G.induce (F : Set V)).Reachable x y)
    {u v : V} (uc : u∈C.support) (vc : v∈C.support) (ux : G.Adj u x.val) (yv : G.Adj y.val v) : u=v := by
  classical
  by_contra different
  obtain ⟨s,hs⟩ := reach.exists_isPath
  let emb := (Embedding.induce (G:=G) (F : Set V)).toHom
  let q : G.Walk x.val y.val := s.map emb
  have qp : q.IsPath := hs.map Subtype.val_injective
  have inF {z : V} (h : z∈q.support) : z∈F := by
    rw [show q.support=s.support.map emb from Walk.support_map _ _] at h
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact w.property
  have absent (z : V) (zc : z∈C.support) : z∉q.support := fun h => (away z (inF h)).2 zc
  let l := Walk.cons ux (q.concat yv)
  have lp : l.IsPath := (Walk.cons_isPath_iff _ _).mpr ⟨qp.concat (absent v vc) yv,by
    rw [Walk.support_concat,List.mem_append]
    exact not_or.mpr ⟨absent u uc,by simpa using different⟩⟩
  obtain ⟨_,_,join⟩ := Graph189TwoExteriorLinks.cycle_routes C hc
  obtain ⟨h,hp,len,inside⟩ := join v (List.mem_toFinset.mpr vc) u (List.mem_toFinset.mpr uc) (Ne.symm different)
  have beg : v∉h.support.tail := by
    have nd := hp.support_nodup
    rw [←h.cons_tail_support] at nd
    exact (List.nodup_cons.mp nd).1
  have dis : l.support.tail.Disjoint h.support.tail := by
    rw [show l.support.tail=(q.concat yv).support by rfl,Walk.support_concat,List.disjoint_left]
    intro z hz ht
    rcases List.mem_append.mp hz with on|last
    · exact (away z (inF on)).2 (List.mem_toFinset.mp (inside z (List.mem_of_mem_tail ht)))
    · have e := List.mem_singleton.mp last
      exact beg (e ▸ ht)
  have enough : 1≤q.length := by
    have n := s.not_nil_of_ne xy
    have h := Walk.not_nil_iff_lt_length.mp n
    change 1≤(s.map emb).length
    rw [Walk.length_map]
    omega
  have hlen := h.length_support
  have cycle := lp.isCycle_append hp dis (Or.inr (by omega))
  have low := bound (l.append h) cycle (by
    intro z hz
    rcases (Walk.mem_support_append_iff _ _).mp hz with head|tail
    · change z∈(Walk.cons ux (q.concat yv)).support at head
      simp only [Walk.support_cons,Walk.support_concat,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at head
      rcases head with e|mid|e
      · exact e ▸ off u uc
      · exact (away z (inF mid)).1
      · exact e ▸ off v vc
    · exact off z (List.mem_toFinset.mp (inside z tail)))
  simp only [l,Walk.length_append,Walk.length_cons,Walk.length_concat] at low
  omega

/-- In the complement of the cycle, the component of a vertex needing
three omitted neighbors has at least three members. A two-vertex component
would give the edge's opposite ends distinct anchors. -/
theorem component_three (W F : Finset V)
    (two : ∀ v∈F, (G.neighborFinset v∩W).card≤2)
    (min : ∀ v∈F, ∀ w∈F, G.Adj v w → 2≤(G.neighborFinset v∩W).card+(G.neighborFinset v∩F).card)
    (unique : ∀ (x y : F), x≠y → (G.induce (F : Set V)).Reachable x y →
      ∀ u∈W, ∀ v∈W, G.Adj u x.val → G.Adj y.val v → u=v)
    (x : F) (many : 3≤(G.neighborFinset x.val∩W).card+(G.neighborFinset x.val∩F).card) :
    3≤(F.filter (fun v => ∃ h : v∈F, (G.induce (F : Set V)).Reachable x ⟨v,h⟩)).card := by
  classical
  let J := G.induce (F : Set V)
  let T := F.filter (fun v => ∃ h : v∈F, J.Reachable x ⟨v,h⟩)
  by_contra! small
  change T.card<3 at small
  have neighbors {v : F} (tv : J.Reachable x v) : (G.neighborFinset v.val∩F)⊆T.erase v.val := by
    intro u hu
    obtain ⟨vu,uf⟩ := mem_inter.mp hu
    have e := (G.mem_neighborFinset _ _).mp vu
    have step : J.Adj v (⟨u,uf⟩ : F) := e
    exact mem_erase.mpr ⟨e.ne.symm,mem_filter.mpr ⟨uf,uf,tv.trans step.reachable⟩⟩
  have upper {v : F} (tv : J.Reachable x v) : (G.neighborFinset v.val∩F).card≤1 := by
    have h := card_le_card (neighbors tv)
    rw [card_erase_of_mem (mem_filter.mpr ⟨v.property,v.property,tv⟩ : v.val∈T)] at h
    change (G.neighborFinset v.val∩F).card≤T.card-1 at h
    omega
  have a := upper (v:=x) Reachable.rfl
  have ap := two x.val x.property
  obtain ⟨y,yn⟩ := card_pos.mp (show 0<(G.neighborFinset x.val∩F).card by omega)
  obtain ⟨xy,yF⟩ := mem_inter.mp yn
  let Y : F := ⟨y,yF⟩
  have step : J.Adj x Y := (G.mem_neighborFinset _ _).mp xy
  have smallY := upper step.reachable
  change (G.neighborFinset y∩F).card≤1 at smallY
  have needY := min y yF x.val x.property step.symm
  obtain ⟨v,vn⟩ := card_pos.mp (show 0<(G.neighborFinset y∩W).card by omega)
  obtain ⟨u,un,uv⟩ := exists_mem_ne (show 1<(G.neighborFinset x.val∩W).card by omega) v
  exact uv (unique x Y step.ne step.reachable u (mem_inter.mp un).2 v (mem_inter.mp vn).2
    ((G.mem_neighborFinset _ _).mp (mem_inter.mp un).1).symm ((G.mem_neighborFinset _ _).mp (mem_inter.mp vn).1))

#print axioms same_anchor
#print axioms component_three
end Graph189FiveCycleLinks
