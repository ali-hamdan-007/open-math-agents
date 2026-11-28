import Graph189FourTriangle
import Graph189FourRoutes
import Graph189SmallComponentOrder
import Graph189BoundaryMatching

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FourExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- A genuine exterior component, in the original vertex type, with its closed boundary. -/
theorem exterior_component (p : G.Walk a b) {v : V} (off : v∉p.support) :
    ∃ W : Finset V, v∈W ∧ (G.induce (W : Set V)).Connected ∧
      (∀ w∈W, w∉p.support) ∧ (∀ w∈W, ∀ z, G.Adj w z → z∉W → z∈p.support) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  let H := G.induce (E : Set V)
  let x : E := ⟨v,by simpa [E] using off⟩
  let C := H.connectedComponentMk x
  let emb : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let W := C.supp.toFinset.map emb
  have mem {z : V} : z∈W ↔ ∃ t : E, t∈C.supp ∧ t.val=z := by simp [W,emb]
  let f : C.toSimpleGraph →g G.induce (W : Set V) := {
    toFun := fun t => ⟨t.val.val,mem.mpr ⟨t.val,t.property,rfl⟩⟩
    map_rel' := fun h => h }
  refine ⟨W,mem.mpr ⟨x,rfl,rfl⟩,C.connected_toSimpleGraph.map f ?_,?_,?_⟩
  · intro w
    obtain ⟨t,ht,e⟩ := mem.mp w.property
    exact ⟨⟨t,ht⟩,Subtype.ext e⟩
  · intro w hw
    obtain ⟨t,_,rfl⟩ := mem.mp hw
    exact fun h => (mem_compl.mp t.property) (List.mem_toFinset.mpr h)
  · intro w hw z edge absent
    by_contra missing
    let z' : E := ⟨z,by simpa [E] using missing⟩
    obtain ⟨t,ht,rfl⟩ := mem.mp hw
    have near : H.Adj t z' := edge
    exact absent (mem.mpr ⟨z',C.mem_supp_of_adj_mem_supp ht near,rfl⟩)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Two-connectivity gives two ordered marks with distinct endpoints in an exterior component. -/
theorem two_ports (p : G.Walk a b) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ w∈W, w∉p.support)
    (boundary : ∀ w∈W, ∀ z, G.Adj w z → z∉W → z∈p.support)
    (size : 2 ≤ W.card) (space : 2 ≤ p.support.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected) :
    ∃ (i j : Fin p.support.length) (u v : W), i<j ∧ u≠v ∧
      G.Adj p.support[i.val] u.val ∧ G.Adj p.support[j.val] v.val := by
  classical
  obtain ⟨A,sub,sz,f,links⟩ := matching_at_component_boundary (G:=G) p.support.toFinset W
    (disjoint_left.mpr (fun _ h hw => outside _ hw (List.mem_toFinset.mp h)))
    (fun w hw z hz edge => List.mem_toFinset.mpr (boundary w hw z edge hz))
    (by rwa [List.toFinset_card_of_nodup hp.support_nodup]) size cuts
  obtain ⟨x,hx,y,hy,ne⟩ := one_lt_card.mp sz
  let X : A := ⟨x,hx⟩
  let Y : A := ⟨y,hy⟩
  have diff : f X ≠ f Y := fun e => ne (congrArg Subtype.val (f.injective e))
  obtain ⟨i,hi,ei⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (sub hx))
  obtain ⟨j,hj,ej⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp (sub hy))
  let I : Fin p.support.length := ⟨i,hi⟩
  let J : Fin p.support.length := ⟨j,hj⟩
  have eI : G.Adj p.support[I.val] (f X).val := by simpa [I,ei] using links X
  have eJ : G.Adj p.support[J.val] (f Y).val := by simpa [J,ej] using links Y
  have distinct : i≠j := by rintro rfl; exact ne (ei.symm.trans ej)
  rcases lt_or_gt_of_ne distinct with lt|gt
  · exact ⟨I,J,f X,f Y,lt,diff,eI,eJ⟩
  · exact ⟨J,I,f Y,f X,gt,diff.symm,eJ,eI⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem mapped {W : Finset V} (p : G.Walk a b) (outside : ∀ z∈W, z∉p.support)
    {u v : W} (q : (G.induce (W : Set V)).Walk u v) (hq : q.IsPath) :
    ∃ r : G.Walk u.val v.val, r.IsPath ∧ List.Disjoint r.support p.support ∧ r.support.length=q.support.length := by
  let inc := (Embedding.induce (G:=G) (W : Set V)).toHom
  have ds : List.Disjoint (q.map inc).support p.support := by
    rw [Walk.support_map,List.disjoint_left]
    intro z hz
    obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
    exact outside t.val t.property
  have len : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  exact ⟨q.map inc,hq.map Subtype.val_injective,ds,len⟩

/-- Two rooted exterior tails and a route between two distinct ports give disjoint lower bounds. -/
theorem detour_order (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support)
    {i j : Fin p.support.length} {u v : W}
    (ij : i<j) (left : G.Adj p.support[i.val] u.val) (right : G.Adj p.support[j.val] v.val)
    (t d : ℕ)
    (tails : ∀ z : W, ∃ w, ∃ q : (G.induce (W : Set V)).Walk z w, q.IsPath ∧ t ≤ q.support.length)
    (inner : ∃ q : (G.induce (W : Set V)).Walk u v, q.IsPath ∧ d ≤ q.support.length) :
    2*t+d+2 ≤ p.support.length := by
  obtain ⟨_,q,hq,l⟩ := tails u
  obtain ⟨r,hr,dis,len⟩ := mapped p outside q hq
  have rc : List.Disjoint r.reverse.support p.support := by simpa [Walk.support_reverse] using dis
  have f := prefix_of_detour p hp longest i r.reverse hr.reverse rc left.symm
  rw [Walk.support_reverse,List.length_reverse,len] at f
  obtain ⟨_,q',hq',l'⟩ := tails v
  obtain ⟨r',hr',dis',len'⟩ := mapped p outside q' hq'
  have g := suffix_of_detour p hp longest j r' hr' dis' right
  rw [len'] at g
  obtain ⟨q'',hq'',l''⟩ := inner
  obtain ⟨r'',hr'',dis'',len''⟩ := mapped p outside q'' hq''
  have h := interval_of_detour p hp longest i j ij r'' hr'' dis'' left right.symm
  rw [len''] at h
  omega

/-- Under the four-witness bound, a longest path in a two-connected graph
of order at most fifteen and minimum degree four cannot omit four vertices
or more. -/
theorem fewer_than_four (p : G.Walk a b) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card < 2 → (G.induce {v : V | v∉U}).Connected)
    (minimum : ∀ v, 4 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w = 2)).card ≤ 4)
    (order : Fintype.card V ≤ 15) :
    (p.support.toFinsetᶜ : Finset V).card < 4 := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card < 4
  by_contra! big
  obtain ⟨v,hv⟩ := card_pos.mp (show 0 < E.card by omega)
  have miss : v∉p.support := by simpa [E] using hv
  obtain ⟨W,vW,conn,out,bd⟩ := exterior_component p miss
  let H := G.induce (W : Set V)
  have raw (w : V) (off : w∉p.support) : 2 ≤ (G.neighborFinset w \ p.support.toFinset).card := by
    have d := (high_exterior_half p hp longest off (quota w) (minimum w)
      (fun u => by have := minimum u; omega) (fun u _ hu _ => by have := minimum u; omega)).2
    have := minimum w
    omega
  have deg (w : W) : 2 ≤ H.degree w := by
    change 2 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact raw w.val (out w.val w.property)
  have Wlarge : 3 ≤ W.card := by
    let w : W := ⟨v,vW⟩
    have bound := H.degree_lt_card_verts w
    change H.degree w < Fintype.card W at bound
    rw [Fintype.card_coe] at bound
    have := deg w
    omega
  have space : 2 ≤ p.support.length := by
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (G.neighborFinset v).card by
      rw [G.card_neighborFinset_eq_degree]; have := minimum v; omega)
    have edge := (G.mem_neighborFinset _ _).mp hz
    have len := longest edge.toWalk edge.isPath_toWalk
    rw [edge.length_toWalk] at len
    have := p.length_support
    omega
  obtain ⟨i,j,u,w,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  have connected : ∃ q : H.Walk u w, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u w
    have nz : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  have b₁ := detour_order p hp longest W out ij left right 3 2
    (Graph189FourRoutes.three_from H deg) connected
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have Wsub : W ⊆ E := fun z hz => by simpa [E] using out z hz
  have Wsmall : Fintype.card W ≤ 5 := by rw [Fintype.card_coe]; have := card_le_card Wsub; omega
  have route := Graph189FourRoutes.three_between H Wsmall deg u w ne
  have b₂ := detour_order p hp longest W out ij left right 3 3 (Graph189FourRoutes.three_from H deg) route
  have Efour : E.card=4 := by omega
  have whole : W=E := by
    apply eq_of_subset_of_card_le Wsub
    by_contra! small
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (E \ W).card by rw [card_sdiff_of_subset Wsub]; omega)
    obtain ⟨zE,zW⟩ := mem_sdiff.mp hz
    let N := G.neighborFinset z \ p.support.toFinset
    have incl : insert z N ⊆ E \ W := by
      intro t ht
      rcases mem_insert.mp ht with rfl|member
      · exact hz
      obtain ⟨edge,off⟩ := mem_sdiff.mp member
      have tm : t∈E := mem_compl.mpr off
      refine mem_sdiff.mpr ⟨tm,fun tw => ?_⟩
      have bad := bd t tw z ((G.mem_neighborFinset _ _).mp edge).symm zW
      exact (mem_compl.mp zE) (List.mem_toFinset.mpr bad)
    have bound := card_le_card incl
    have notself : z∉N := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
    rw [card_insert_of_notMem notself,card_sdiff_of_subset Wsub] at bound
    have low : 2 ≤ N.card := raw z (by simpa [E] using zE)
    omega
  have four : Fintype.card W=4 := by rw [Fintype.card_coe,whole,Efour]
  have b₃ := detour_order p hp longest W out ij left right 4 3 (Graph189FourRoutes.four_from H four deg) route
  omega

#print axioms fewer_than_four
end Graph189FourExterior
