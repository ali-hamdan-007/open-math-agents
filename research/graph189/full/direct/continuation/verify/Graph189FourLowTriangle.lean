import Graph189FourLowTriangleData
import Graph189FourTerminalGap
import Graph189GapExchange

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourLowTriangle
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

private theorem no_triangle_through (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (on : z∈p.support) (degree : ∀ v, v≠z → 4 ≤ G.degree v)
    (retain : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length=p.length →
      ∀ w, w≠z → w∉r.support → 2 ≤ (G.neighborFinset w \ r.support.toFinset).card)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 4)
    (order : Fintype.card V ≤ 14) (size : (p.support.toFinsetᶜ : Finset V).card=3) : False := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=3 at size
  obtain ⟨plen,routes,rows⟩ := data p hp maximal z degree (retain p hp rfl) order size
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp (show 1 < E.card by omega)
  let X : E := ⟨x,hx⟩
  let Y : E := ⟨y,hy⟩
  have off {w : V} (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have nz {w : V} (hw : w∈E) : w≠z := fun e => off hw (e ▸ on)
  obtain ⟨w,hw⟩ := routes X Y (fun h => ne (congrArg Subtype.val h))
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact off u.property
  have qlen : q.support.length=3 := by
    change (w.map inc).support.length=3
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=3
    rwa [Fintype.card_coe]
  let I : Fin p.support.length := ⟨3,by omega⟩
  let J : Fin p.support.length := ⟨7,by omega⟩
  let M : Finset (Fin p.support.length) := {I,J}
  have touching (i : Fin p.support.length) (hi : i∈M) (w : V) (hw : w∈E) : G.Adj p.support[i.val] w := by
    have hit : i.val∈contactPositions p w := by
      rw [rows w hw (nz hw)]
      rcases mem_insert.mp hi with rfl|other
      · simp [I]
      · obtain rfl := mem_singleton.mp other
        simp [J]
    simpa only [get_at] using ((mem_contactPositions p w i.val).mp hit).2
  have touch (i : Fin p.support.length) (hi : i∈M) := And.intro (touching i hi x hx) (touching i hi y hy)
  obtain ⟨n,rn,value⟩ := List.mem_iff_getElem.mp on
  let t : Fin p.support.length := ⟨n,rn⟩
  have uniform {c d} (r : G.Walk c d) (hr : r.IsPath) (keep : p.support[t.val]∈r.support) (same : r.length=p.length)
      (v : V) (hv : v∈r.support) (x : V) (ox : x∉r.support) (y : V) (oy : y∉r.support) (vx : G.Adj v x) : G.Adj v y := by
    have zIn : z∈r.support := by simpa only [t,value] using keep
    have count := card_add_card_compl p.support.toFinset
    have count' := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hp.support_nodup] at count
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count'
    change p.support.length+E.card=Fintype.card V at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    obtain ⟨_,_,all⟩ := data r hr (fun q h => by rw [same]; exact maximal q h) z degree (retain r hr same) order (by omega)
    have eqx := all x (by simpa using ox) (fun e => ox (e ▸ zIn))
    have eqy := all y (by simpa using oy) (fun e => oy (e ▸ zIn))
    obtain ⟨l,rl,ev⟩ := List.mem_iff_getElem.mp hv
    have hit : l∈contactPositions r x := (mem_contactPositions r x l).mpr ⟨rl,by rwa [←get_at r rl,ev]⟩
    rw [eqx,←eqy] at hit
    simpa only [←get_at r rl,ev] using ((mem_contactPositions r y l).mp hit).2
  have marked := rows x hx (nz hx)
  by_cases early : n<3
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform (lo:=8) (hi:=11)
      (by decide) plen.ge (by omega) (Or.inl (by change n<8; omega))
      (Or.inr ⟨J,by simp [M],rfl⟩) (Or.inl plen.symm) (Or.inl (by decide))
    apply Graph189FourTerminalGap.impossible_of_exact p hp (off hx) (by decide) (by decide) (by omega) marked
      plen.ge rfl _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega
  · have via := interval_exchange_witnesses p hp t M q hq dis touch uniform (lo:=0) (hi:=3)
      (by decide) (by omega) (by omega) (Or.inr (by change 3 ≤ n; omega)) (Or.inl rfl)
      (Or.inr ⟨I,by simp [M],rfl⟩) (Or.inr (by omega))
    apply Graph189FourTerminalGap.impossible_of_exact p hp (off hx) (by decide) (by decide) (by omega) marked
      (by omega) (by decide : 0+3=3) _ via (quota x)
    intro l hl
    have := mem_Ico.mp hl
    omega

/-- Three omissions are impossible even if the original path omits the
unique low vertex. In that case the tight prefix exchange first produces a
longest path containing the low vertex. -/
theorem no_triangle (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (z : V) (degree : ∀ v, v≠z → 4 ≤ G.degree v)
    (retain : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length=p.length →
      ∀ w, w≠z → w∉r.support → 2 ≤ (G.neighborFinset w \ r.support.toFinset).card)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 4)
    (order : Fintype.card V ≤ 14) (size : (p.support.toFinsetᶜ : Finset V).card=3) : False := by
  classical
  by_cases old : z∈p.support
  · exact no_triangle_through p hp maximal z old degree retain quota order size
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=3 at size
  obtain ⟨plen,routes,rows⟩ := data p hp maximal z degree (retain p hp rfl) order size
  obtain ⟨y,hy,yz⟩ := exists_mem_ne (show 1 < E.card by omega) z
  let Z : E := ⟨z,by simpa [E] using old⟩
  let Y : E := ⟨y,hy⟩
  obtain ⟨w,hw⟩ := routes Z Y (fun e => yz (congrArg Subtype.val e).symm)
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact fun h => (mem_compl.mp u.property) (List.mem_toFinset.mpr h)
  have qlen : q.support.length=3 := by
    change (w.map inc).support.length=3
    rw [Walk.support_map,List.length_map,hw.length_support]
    change Fintype.card E=3
    rwa [Fintype.card_coe]
  have e : G.Adj y p.support[3] := by
    have mark : 3∈contactPositions p y := by rw [rows y hy yz]; simp
    have edge := ((mem_contactPositions p y 3).mp mark).2
    simpa only [get_at] using edge.symm
  obtain ⟨a',b',r,hr,supp⟩ := splice_support p hp [] (p.support.take 3) (p.support.drop 3)
    (by simp) q hq dis (by simp) (by
      intro v hv
      have head : (p.support.drop 3).head?=some p.support[3] := by simp [List.head?_drop]
      have value : p.support[3]=v := by simpa only [head,Option.mem_def,Option.some.injEq] using hv
      exact value ▸ e)
  have rz : z∈r.support := by
    rw [supp,List.nil_append,List.mem_append]
    exact Or.inl (show inc Z ∈ q.support from q.start_mem_support)
  have rr : r.support.length=p.support.length := by rw [supp]; simp [qlen,plen]
  have len : r.length=p.length := by have := p.length_support; have := r.length_support; omega
  have aSize := card_add_card_compl p.support.toFinset
  have bSize := card_add_card_compl r.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at aSize
  rw [List.toFinset_card_of_nodup hr.support_nodup] at bSize
  change p.support.length+E.card=Fintype.card V at aSize
  apply no_triangle_through r hr (fun q h => by rw [len]; exact maximal q h) z rz degree
    (fun q h same => retain q h (same.trans len)) quota order (by omega)

#print axioms no_triangle
end Graph189FourLowTriangle
