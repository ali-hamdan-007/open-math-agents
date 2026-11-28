import Graph189ThreeExteriorLinks
import Graph189SixFullPorts
import Graph189FivePortOrder

open SimpleGraph Finset Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189SixWideRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At second degree six and minimum degree at least three, a longest path
of order at most twenty-five, with all exterior cycles of length at most four, omits no high vertex. -/
theorem no_high_of_cycle_cap {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (limit : ∀ {r : V}, ∀ C : G.Walk r r, C.IsCycle → (∀ v∈C.support,v∉p.support) → C.length≤4) (order : Fintype.card V≤25)
    (six : G.secondSmallestDegree=6) (minimum : ∀ v, 3≤G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤6)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 6≤G.degree highVertex) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let f : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique {a b : E} (la : G.degree a.val<6) (lb : G.degree b.val<6) : a=b := by
    apply Subtype.ext
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) _ _ ne
    omega
  obtain ⟨degree,B,R,rank,sub,width,trapped⟩ := Graph189OrdinaryRotationWindow.of_cycle_cap p hp mx
    (d:=3) (L:=4) six (by decide) (by decide) (by decide) (fun C hc out => limit C hc out) minimum quota omitted large
  let H := fun a : E => 6≤G.degree a.val
  let D := B.filter (fun a => H a ∧ J.neighborFinset a⊆B)
  have good {a : E} (ar : a∈R) (hi : H a) : a∈D := mem_filter.mpr ⟨sub ar,hi,trapped a ar⟩
  have few : (R\D).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb
    apply unique
    · by_contra! hi
      exact (mem_sdiff.mp ha).2 (good (mem_sdiff.mp ha).1 hi)
    · by_contra! hi
      exact (mem_sdiff.mp hb).2 (good (mem_sdiff.mp hb).1 hi)
  have split := card_sdiff_add_card_inter R D
  have common : (R∩D).card≤D.card := card_le_card inter_subset_right
  have two : 2≤D.card := by omega
  have full {a : E} (ha : a∈D) : J.neighborFinset a=B.erase a ∧ B.card=4 := by
    obtain ⟨ab,hi,trap⟩ := mem_filter.mp ha
    have deg : 3≤J.degree a := degree a hi
    have inc : J.neighborFinset a⊆B.erase a := by
      intro v hv
      exact mem_erase.mpr ⟨((J.mem_neighborFinset _ _).mp hv).ne.symm,trap hv⟩
    have h := card_le_card inc
    rw [J.card_neighborFinset_eq_degree,card_erase_of_mem ab] at h
    exact ⟨eq_of_subset_of_card_le inc (by
      rw [J.card_neighborFinset_eq_degree,card_erase_of_mem ab]
      omega),by omega⟩
  obtain ⟨a,ha,b,hb,ab⟩ := one_lt_card.mp (show 1<D.card by omega)
  have size := (full ha).2
  have edge {u v : E} (hu : u∈D) (hv : v∈B) (diff : u≠v) : J.Adj u v := by
    apply (J.mem_neighborFinset _ _).mp
    rw [(full hu).1]
    exact mem_erase.mpr ⟨diff.symm,hv⟩
  by_cases three : 3≤D.card
  · have incl : D.map f⊆B.map f := map_subset_map.mpr (filter_subset _ _)
    have outside (v : V) (hv : v∈B.map f) : v∉p.support := by
      obtain ⟨u,_,rfl⟩ := mem_map.mp hv
      exact off u
    have boundary (v : V) (hv : v∈D.map f) (w : V) (vw : G.Adj v w) (no : w∉B.map f) : w∈p.support := by
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      by_contra miss
      let j : E := ⟨w,mem_compl.mpr fun h => miss (List.mem_toFinset.mp h)⟩
      have step : J.Adj u j := vw
      exact no (mem_map.mpr ⟨j,(mem_filter.mp hu).2.2 ((J.mem_neighborFinset _ _).mpr step),rfl⟩)
    have high (v : V) (hv : v∈D.map f) : 6≤G.degree v := by
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      exact (mem_filter.mp hu).2.1
    have clique : G.IsClique ((B.map f) : Set V) := by
      intro v hv w hw ne
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hw
      have distinct : u≠v := fun e => ne (congrArg f e)
      by_cases ud : u∈D
      · exact edge ud hv distinct
      by_cases vd : v∈D
      · exact (edge vd hu distinct.symm).symm
      have count := card_sdiff_add_card_eq_card (show D⊆B from filter_subset _ _)
      have one : (B\D).card≤1 := by omega
      exact False.elim (distinct (card_le_one.mp one u (mem_sdiff.mpr ⟨hu,ud⟩) v (mem_sdiff.mpr ⟨hv,vd⟩)))
    have l := Graph189SixFullPorts.initial p hp mx (B.map f) (D.map f) (by rwa [card_map])
      (by rwa [card_map]) incl outside clique boundary high quota order
    have r := Graph189SixFullPorts.initial p.reverse hp.reverse (fun q hq => by simpa using mx q hq)
      (B.map f) (D.map f) (by rwa [card_map]) (by rwa [card_map]) incl
      (fun v hv => by simpa using outside v hv) clique
      (fun u hu v e skip => by simpa using boundary u hu v e skip) high quota order
    have xy : x≠y := by
      intro eq
      subst y
      have zero := (Walk.isPath_iff_nil.mp hp).length_eq_zero
      have adj : G.Adj a.val b.val := edge ha (mem_filter.mp hb).1 ab
      have atLeast := mx adj.toWalk adj.isPath_toWalk
      rw [adj.length_toWalk] at atLeast
      omega
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) x y xy
    omega
  obtain ⟨z,zr,low⟩ : ∃ z∈R, ¬H z := by
    by_contra! all
    have inc : R⊆D := fun u hu => good hu (all u hu)
    have := card_le_card inc
    omega
  have wc : ∃ c∈B, c∉R := by
    by_contra! inc
    have same : B=R := Subset.antisymm inc sub
    have bad : (B\D).card≤1 := by simpa only [same] using few
    have h := card_sdiff_add_card_eq_card (show D⊆B from filter_subset _ _)
    omega
  obtain ⟨c,cb,cr⟩ := wc
  have rest : B.erase c=R := by
    apply (eq_of_subset_of_card_le (show R⊆B.erase c from fun v vr =>
      mem_erase.mpr ⟨fun eq => cr (eq ▸ vr),sub vr⟩) ?_).symm
    rw [card_erase_of_mem cb,size]
    omega
  have others {u : E} (ub : u∈B) (diff : u≠c) : u∈R := by
    rw [←rest]
    exact mem_erase.mpr ⟨diff,ub⟩
  have cz : c≠z := fun h => cr (h ▸ zr)
  have hi_c : H c := by
    by_contra lo
    exact cz (unique (Nat.lt_of_not_ge lo) (Nat.lt_of_not_ge low))
  have cd : c∉D := by
    intro hc
    have inc : insert c (R∩D)⊆D := insert_subset hc inter_subset_right
    have h := card_le_card inc
    rw [card_insert_of_notMem (fun e => cr (mem_inter.mp e).1)] at h
    omega
  obtain ⟨w,neighbor,wb⟩ : ∃ w∈J.neighborFinset c,w∉B := by
    by_contra! confined
    exact cd (mem_filter.mpr ⟨cb,hi_c,confined⟩)
  have cw := (J.mem_neighborFinset _ _).mp neighbor
  have hi_w : H w := by
    by_contra lo
    have wz := unique (Nat.lt_of_not_ge lo) (Nat.lt_of_not_ge low)
    exact wb (wz ▸ sub zr)
  have outside : insert w ((J.neighborFinset w).erase c)⊆Bᶜ := by
    intro v hv
    apply mem_compl.mpr
    rcases mem_insert.mp hv with rfl|h
    · exact wb
    intro vb
    obtain ⟨ne,nv⟩ := mem_erase.mp h
    have vr := others vb ne
    exact wb (trapped v vr ((J.mem_neighborFinset _ _).mpr ((J.mem_neighborFinset _ _).mp nv).symm))
  have lower := card_le_card outside
  have self : w∉(J.neighborFinset w).erase c := fun e => ((J.mem_neighborFinset _ _).mp (mem_erase.mp e).2).ne rfl
  rw [card_insert_of_notMem self,card_erase_of_mem ((J.mem_neighborFinset _ _).mpr cw.symm),
    J.card_neighborFinset_eq_degree] at lower
  have grow : 3≤J.degree w := degree w hi_w
  have totalB := card_add_card_compl B
  have ambient := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at ambient
  change p.support.length+E.card=Fintype.card V at ambient
  change B.card+Bᶜ.card=Fintype.card E at totalB
  rw [Fintype.card_coe] at totalB
  have short : p.support.length≤18 := by omega
  have degreeBeyond {x : E} (xb : x∉B) : 3≤J.degree x := by
    apply degree
    by_contra! lo
    have eq := unique lo (Nat.lt_of_not_ge low)
    exact xb (eq ▸ sub zr)
  have other {x : E} (xb : x∉B) : 2≤((J.neighborFinset x).erase c).card := by
    have de := degreeBeyond xb
    by_cases e : c∈J.neighborFinset x
    · rw [card_erase_of_mem e,J.card_neighborFinset_eq_degree]
      omega
    · rw [erase_eq_of_notMem e,J.card_neighborFinset_eq_degree]
      omega
  have away {x u : E} (xb : x∉B) (hu : u∈(J.neighborFinset x).erase c) : u∉B := by
    intro ub
    obtain ⟨uc,edge⟩ := mem_erase.mp hu
    exact xb (trapped u (others ub uc) ((J.mem_neighborFinset _ _).mpr ((J.mem_neighborFinset _ _).mp edge).symm))
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<((J.neighborFinset w).erase c).card by have := other wb; omega)
  have ub := away wb hu
  obtain ⟨v,hv,vw⟩ := exists_mem_ne (show 1<((J.neighborFinset u).erase c).card by have := other ub; omega) w
  have vb := away ub hv
  have wu := (J.mem_neighborFinset _ _).mp (mem_erase.mp hu).2
  have uv := (J.mem_neighborFinset _ _).mp (mem_erase.mp hv).2
  have au : a≠u := fun e => ub (e ▸ (mem_filter.mp ha).1)
  have bu : b≠u := fun e => ub (e ▸ (mem_filter.mp hb).1)
  have av : a≠v := fun e => vb (e ▸ (mem_filter.mp ha).1)
  have bv : b≠v := fun e => vb (e ▸ (mem_filter.mp hb).1)
  have zu : z≠u := fun e => ub (e ▸ sub zr)
  have zv : z≠v := fun e => vb (e ▸ sub zr)
  have cu : c≠u := fun e => ub (e ▸ cb)
  have cv : c≠v := fun e => vb (e ▸ cb)
  have mark {u : E} (hu : u∈D) : 3≤(contactPositions p u.val).card := by
    have de := (full hu).1
    have int : J.degree u=3 := by
      rw [←J.card_neighborFinset_eq_degree,de,card_erase_of_mem (mem_filter.mp hu).1,size]
    have eq : J.degree u=(G.neighborFinset u.val\p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    rw [contact_card_neighbors p hp]
    have cnt := card_sdiff_add_card_inter (G.neighborFinset u.val) p.support.toFinset
    have hi := (mem_filter.mp hu).2.1
    change 6≤G.degree u.val at hi
    rw [G.card_neighborFinset_eq_degree] at cnt
    omega
  obtain ⟨i,mi⟩ := card_pos.mp (show 0<(contactPositions p a.val).card by have := mark ha; omega)
  obtain ⟨j,mj,ji⟩ := exists_mem_ne (show 1<(contactPositions p b.val).card by have := mark hb; omega) i
  have ti := (mem_contactPositions p a.val i).mp mi
  have tj := (mem_contactPositions p b.val j).mp mj
  let I : Fin p.support.length := ⟨i,ti.1⟩
  let K : Fin p.support.length := ⟨j,tj.1⟩
  have ia : G.Adj p.support[I.val] a.val := by simpa only [I,get_at] using ti.2
  have jb : G.Adj p.support[K.val] b.val := by simpa only [K,get_at] using tj.2
  have distinct {u : E} (hu : u∈D) : u≠z ∧ u≠c ∧ u≠w := by
    exact ⟨fun e => low (e ▸ (mem_filter.mp hu).2.1),fun e => cd (e ▸ hu),
      fun e => wb (e ▸ (mem_filter.mp hu).1)⟩
  have az := distinct ha
  have bz := distinct hb
  have zw : z≠w := fun e => wb (e ▸ sub zr)
  have eaz := edge ha (sub zr) az.1
  have ebz := edge hb (sub zr) bz.1
  have eac := edge ha cb az.2.1
  have ebc := edge hb cb bz.2.1
  let ta := Walk.cons eaz (Walk.cons ebz.symm (Walk.cons ebc (Walk.cons cw (Walk.cons wu (Walk.cons uv .nil)))))
  let tb := Walk.cons ebz (Walk.cons eaz.symm (Walk.cons eac (Walk.cons cw (Walk.cons wu (Walk.cons uv .nil)))))
  let middle := Walk.cons eaz (Walk.cons ebz.symm .nil)
  have pa : ta.IsPath := Walk.IsPath.mk' (by
    simp [ta,az.1,ab,az.2.1,az.2.2,bz.1.symm,cz.symm,zw,bz.2.1,bz.2.2,cw.ne,au,bu,av,bv,zu,zv,cu,cv,wu.ne,vw.symm,uv.ne])
  have pb : tb.IsPath := Walk.IsPath.mk' (by
    simp [tb,bz.1,ab.symm,bz.2.1,bz.2.2,az.1.symm,cz.symm,zw,az.2.1,az.2.2,cw.ne,au,bu,av,bv,zu,zv,cu,cv,wu.ne,vw.symm,uv.ne])
  have pm : middle.IsPath := Walk.IsPath.mk' (by simp [middle,az.1,ab,bz.1.symm])
  have out (v : V) (hv : v∈E) : v∉p.support := off ⟨v,hv⟩
  have diff : I≠K := fun e => ji (congrArg Fin.val e).symm
  rcases lt_or_gt_of_ne diff with forward|backward
  · have n := Graph189FivePortOrder.order p hp mx E out forward ia jb 7 7 3
      ⟨v,ta,pa,by simp [ta]⟩ ⟨v,tb,pb,by simp [tb]⟩ ⟨middle,pm,by simp [middle]⟩
    omega
  · have n := Graph189FivePortOrder.order p hp mx E out backward jb ia 7 7 3
      ⟨v,tb,pb,by simp [tb]⟩ ⟨v,ta,pa,by simp [ta]⟩ ⟨middle.reverse,pm.reverse,by simp [middle]⟩
    omega

/-- Three disjoint links supply the four-cycle bound at order twenty-five. -/
theorem no_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length≤p.length)
    (conn : 3≤G.vertexConnectivity) (order : Fintype.card V≤25)
    (six : G.secondSmallestDegree=6) (minimum : ∀ v, 3≤G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤6)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 6≤G.degree highVertex) : False := by
  have limit {r : V} (C : G.Walk r r) (hc : C.IsCycle) (away : ∀ v∈C.support,v∉p.support) : C.length≤4 := by
    have n := Graph189ThreeExteriorLinks.order_of_cycle p hp mx conn C hc away
    omega
  exact no_high_of_cycle_cap p hp mx (fun C hc away => limit C hc away) order six minimum quota omitted large

end Graph189SixWideRotation
#print axioms Graph189SixWideRotation.no_high
