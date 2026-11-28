import Graph189FiveCycleIsolated

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveCycleAttached
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}

omit [DecidableEq V] in
theorem finite_rows [DecidableRel G.Adj] (p : G.Walk a b) (u : V) :
    ((univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] u)).card =
      (contactPositions p u).card := by
  classical
  let F := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] u)
  have eq : F.image Fin.val=contactPositions p u := by
    ext i
    constructor
    · intro h
      obtain ⟨j,jF,rfl⟩ := mem_image.mp h
      exact (mem_contactPositions _ _ _).mpr ⟨j.isLt,by simpa only [get_at] using (mem_filter.mp jF).2⟩
    · intro h
      obtain ⟨valid,ed⟩ := (mem_contactPositions _ _ _).mp h
      exact mem_image.mpr ⟨⟨i,valid⟩,mem_filter.mpr ⟨mem_univ _,by change G.Adj p.support[i] u; rwa [get_at]⟩,rfl⟩
  rw [←eq,card_image_of_injective _ Fin.val_injective]

variable [Fintype V] [Nontrivial V] [DecidableRel G.Adj]

/-- A five-cycle with one additional omitted vertex is impossible in the
original two-connected graph. -/
theorem excluded (hcG : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (degree : G.secondSmallestDegree=6) (conn : 2≤G.vertexConnectivity) (minimum : ∀ v, 3≤G.degree v)
    {r : V} (p : G.Walk a b) (hp : p.IsPath) (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (C : G.Walk r r) (hc : C.IsCycle) (five : C.length=5) (off : ∀ v∈C.support,v∉p.support)
    (size : p.support.toFinsetᶜ.card=6) : False := by
  classical
  obtain ⟨w,wp,wc,_,low,high,ext,tw,positive,rich,pl,nl,wd,quota⟩ :=
    Graph189FiveCycleSixData.data hcG cap degree conn minimum p hp mx C hc five off size
  let W := C.support.toFinset
  let S := G.neighborFinset w∩W
  by_cases empty : S=∅
  · exact Graph189FiveCycleIsolated.excluded hcG cap degree conn minimum p hp mx C hc five off size
      wp wc wd low (ext.trans empty) quota
  obtain ⟨u,us⟩ := nonempty_iff_ne_empty.mpr empty
  have wu := (G.mem_neighborFinset _ _).mp (mem_inter.mp us).1
  have uc := List.mem_toFinset.mp (mem_inter.mp us).2
  have half := half_degree_outside_longest p hp mx wp (off u uc) wu quota (high u uc)
  have two : S.card=2 := by
    change G.neighborFinset w\p.support.toFinset=S at ext
    rw [ext] at tw half
    omega
  have dw : G.degree w=4 := by omega
  have point (v : V) : G.distEven v≤7 := by
    have h := (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
    omega
  have n := Graph189QuadraticOrder.rooted hcG w 6 point
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  have order : Fintype.card V=23 := by omega
  have len : p.support.length=17 := by omega
  let D := W\G.neighborFinset w
  have sub : D⊆W := sdiff_subset
  have many : 3≤D.card := by
    have n := card_sdiff_add_card_inter W (G.neighborFinset w)
    rw [inter_comm] at n
    change D.card+S.card=W.card at n
    have five' : W.card=5 := (Graph189SixCycleExtra.cycle_card C hc).trans five
    omega
  have rows (v : V) (vd : v∈D) : 2≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] v)).card := by
    rw [finite_rows]
    exact rich v (List.mem_toFinset.mp (sub vd)) (fun h => (mem_sdiff.mp vd).2 ((G.mem_neighborFinset _ _).mpr h))
  obtain ⟨M,count,all,cover⟩ := Graph189FiveCycleContacts.pair p W D sub many rows (by
    intro M three f edges
    have n := Graph189FiveCycleContacts.triple p hp mx C hc five off M three f edges
    omega)
  obtain ⟨_,d,e,de,noD,noE⟩ := Graph189FiveCycleRing.outside_neighbors hcG cap degree conn p hp mx C hc five off wp wc
  have dd : d∈D := mem_sdiff.mpr ⟨List.mem_toFinset.mpr (C.fst_mem_support_of_mem_edges de),
    fun h => noD ((G.mem_neighborFinset _ _).mp h)⟩
  have ed : e∈D := mem_sdiff.mpr ⟨List.mem_toFinset.mpr (C.snd_mem_support_of_mem_edges de),
    fun h => noE ((G.mem_neighborFinset _ _).mp h)⟩
  have extreme (i : Fin p.support.length) (im : i∈M) : i.val=5 ∨ i.val=11 := by
    obtain ⟨j,jm,ji⟩ := exists_mem_ne (show 1<M.card by omega) i
    have vi := (all d dd i).mpr im
    have vj := (all e ed j).mpr jm
    have m := Graph189FiveCycleSixData.two_marks p hp mx C hc off de
      ((mem_contactPositions _ _ _).mpr ⟨i.isLt,by simpa only [get_at] using vi⟩)
      ((mem_contactPositions _ _ _).mpr ⟨j.isLt,by simpa only [get_at] using vj⟩)
      (fun eq => ji (Fin.ext eq.symm))
    omega
  obtain ⟨v,vs,vu⟩ := exists_mem_ne (show 1<S.card by omega) u
  have wv := (G.mem_neighborFinset _ _).mp (mem_inter.mp vs).1
  have vc := List.mem_toFinset.mp (mem_inter.mp vs).2
  have parts := card_sdiff_add_card_inter (G.neighborFinset w) p.support.toFinset
  rw [ext,G.card_neighborFinset_eq_degree,←contact_card_neighbors p hp] at parts
  change S.card+(contactPositions p w).card=G.degree w at parts
  obtain ⟨i,im⟩ := card_pos.mp (show 0<(contactPositions p w).card by omega)
  obtain ⟨j,jm⟩ := card_pos.mp (show 0<(contactPositions p u).card by have := positive u uc; omega)
  obtain ⟨ii,ci⟩ := (mem_contactPositions _ _ _).mp im
  obtain ⟨jj,cj⟩ := (mem_contactPositions _ _ _).mp jm
  let I : Fin p.support.length := ⟨i,ii⟩
  let J : Fin p.support.length := ⟨j,jj⟩
  have cI : G.Adj p.support[I.val] w := by simpa only [I,get_at] using ci
  have cJ : G.Adj p.support[J.val] u := by simpa only [J,get_at] using cj
  have ex := extreme J (cover u (List.mem_toFinset.mpr uc) J cJ)
  change j=5 ∨ j=11 at ex
  obtain ⟨_,start,join⟩ := Graph189TwoExteriorLinks.cycle_routes C hc
  have extra {x y : V} (wx : G.Adj w x) {q : G.Walk x y} (hq : q.IsPath) (inc : ∀ v∈q.support,v∈C.support.toFinset) :
      (q.cons wx).IsPath ∧ List.Disjoint (q.cons wx).support p.support := by
    exact ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hq,fun h => wc (List.mem_toFinset.mp (inc _ h))⟩,
      List.disjoint_left.mpr (fun t h => (List.mem_cons.mp h).elim (fun e => e ▸ wp)
        (fun hq => off t (List.mem_toFinset.mp (inc t hq))))⟩
  obtain ⟨_,l,lp,long,inside⟩ := start u (List.mem_toFinset.mpr uc)
  obtain ⟨path,away⟩ := extra wu lp inside
  have first := prefix_of_detour p hp mx I (l.cons wu).reverse path.reverse
    (by rw [Walk.support_reverse]; exact List.disjoint_left.mpr fun t ht => List.disjoint_left.mp away (List.mem_reverse.mp ht)) cI.symm
  have last := suffix_of_detour p hp mx I (l.cons wu) path away cI
  rw [Walk.support_reverse,List.length_reverse,Walk.support_cons,List.length_cons] at first
  rw [Walk.support_cons,List.length_cons] at last
  change l.support.length+1≤ i at first
  change i+1+(l.support.length+1)≤p.support.length at last
  obtain ⟨q,hq,ql,inc⟩ := join v (List.mem_toFinset.mpr vc) u (List.mem_toFinset.mpr uc) vu
  obtain ⟨simple,dis⟩ := extra wv hq inc
  by_cases forward : i<j
  · have m := interval_of_detour p hp mx I J (show I<J from forward) (q.cons wv) simple dis cI cJ.symm
    rw [Walk.support_cons,List.length_cons] at m
    change i+1+(q.support.length+1)≤j at m
    omega
  · have back : j < i := by omega
    have m := interval_of_detour p hp mx J I (show J<I from back) (q.cons wv).reverse simple.reverse
      (by rw [Walk.support_reverse]; exact List.disjoint_left.mpr fun t ht => List.disjoint_left.mp dis (List.mem_reverse.mp ht)) cJ cI.symm
    rw [Walk.support_reverse,List.length_reverse,Walk.support_cons,List.length_cons] at m
    change j+1+(q.support.length+1)≤ i at m
    omega

#print axioms excluded
end Graph189FiveCycleAttached
