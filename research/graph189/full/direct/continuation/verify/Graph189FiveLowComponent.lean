import Graph189FiveOneLowRoutes

open Finset SimpleGraph Graph189ExteriorGap Graph189FourExterior
namespace Graph189FiveLowComponent
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- A component containing a high omission has four vertices. The only
other possible omission is an isolated low vertex. -/
theorem classify (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (low : 3 ≤ G.degree z) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (retain : ∀ w, w≠z → w∉p.support → 3 ≤ (G.neighborFinset w \ p.support.toFinset).card)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (limit : Fintype.card V ≤ 19) {x : V} (xz : x≠z) (miss : x∉p.support) :
    (p.support.toFinsetᶜ : Finset V).card=4 ∨
      ((p.support.toFinsetᶜ : Finset V).card=5 ∧ z∉p.support ∧ G.neighborFinset z ⊆ p.support.toFinset) := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4 ∨ E.card=5 ∧ _ ∧ _
  obtain ⟨W,xW,conn,out,bd⟩ := exterior_component p miss
  let H := G.induce (W : Set V)
  have deg (w : W) (wz : w.val≠z) : 3 ≤ H.degree w := by
    change 3 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact retain w wz (out _ w.property)
  have large : 4 ≤ W.card := by
    let x' : W := ⟨x,xW⟩
    have lower := deg x' xz
    have ub := H.degree_lt_card_verts x'
    change H.degree x' < Fintype.card W at ub
    rw [Fintype.card_coe] at ub
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have all (w : W) : 2 ≤ H.degree w := by
    by_cases wz : w.val=z
    · obtain ⟨v,hv⟩ := conn.preconnected.exists_adj_of_nontrivial w
      have vz : v.val≠z := fun e => hv.ne (Subtype.ext (wz.trans e.symm))
      have l := half_degree_outside_longest p hp maximal (out w.val w.property) (out v.val v.property)
        (show G.Adj w.val v.val from hv) (quota w.val) (high v.val vz)
      change 2 ≤ (G.induce (W : Set V)).degree w
      rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
      have dw : 3 ≤ G.degree w.val := wz ▸ low
      omega
    · exact (deg w wz).trans' (by decide)
  have pair (u v : W) (ne : u≠v) : 3 ≤ H.degree u ∨ 3 ≤ H.degree v := by
    by_cases uz : u.val=z
    · exact Or.inr (deg v (fun e => ne (Subtype.ext (uz.trans e.symm))))
    · exact Or.inl (deg u uz)
  have sub : W ⊆ E := fun t ht => by simpa [E] using out t ht
  have le := card_le_card sub
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have space : 2 ≤ p.support.length := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (G.neighborFinset x).card by
      rw [G.card_neighborFinset_eq_degree]; have := high x xz; omega)
    have e := (G.mem_neighborFinset _ _).mp hy
    have bound := maximal e.toWalk e.isPath_toWalk
    rw [e.length_toWalk] at bound
    have := p.length_support
    omega
  obtain ⟨i,j,u,v,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  have base : ∃ q : H.Walk u v, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u v
    have nz : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  have path4 (w : W) := Graph189RootedOneLow.rooted_path (H:=H) w
    (conn.preconnected.exists_adj_of_nontrivial w) pair
  have bound := detour_order p hp maximal W out ij left right 4 2 path4 base
  have more := Graph189FiveOneLowRoutes.three_between H (by change Fintype.card W ≤ 7; rw [Fintype.card_coe]; omega) all pair u v ne
  have bound' := detour_order p hp maximal W out ij left right 4 3 path4 more
  have four : W.card=4 := by
    by_contra other
    have paths := Graph189FiveOneLowRoots.five_from H all pair
      (by change 5 ≤ Fintype.card W; rw [Fintype.card_coe]; omega)
      (by change Fintype.card W ≤ 6; rw [Fintype.card_coe]; omega)
    have impossible := detour_order p hp maximal W out ij left right 5 3 paths more
    omega
  have clique (s t : W) (ne : s≠t) : H.Adj s t := by
    have full (w : W) (wz : w.val≠z) : H.neighborFinset w=univ.erase w := by
      apply eq_of_subset_of_card_le (fun a h => mem_erase.mpr ⟨((H.mem_neighborFinset _ _).mp h).ne.symm,mem_univ _⟩)
      rw [card_erase_of_mem (mem_univ w),card_univ,H.card_neighborFinset_eq_degree]
      rw [Fintype.card_coe,four]
      exact deg w wz
    by_cases sz : s.val=z
    · have f := full t (fun e => ne (Subtype.ext (sz.trans e.symm)))
      exact ((H.mem_neighborFinset _ _).mp (f ▸ mem_erase.mpr ⟨ne,mem_univ _⟩)).symm
    · exact (H.mem_neighborFinset _ _).mp ((full s sz) ▸ mem_erase.mpr ⟨ne.symm,mem_univ _⟩)
  have top : (⊤ : SimpleGraph W) ≤ H := fun s t e => clique s t e.ne
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.complete_prescribed u v ne
  have inner : ∃ q : H.Walk u v, q.IsPath ∧ 4 ≤ q.support.length := by
    refine ⟨q.mapLe top,hq.isPath.mapLe top,?_⟩
    rw [Walk.length_support,Walk.length_mapLe,←q.length_support,hq.length_support,Fintype.card_coe,four]
  have fullLen := detour_order p hp maximal W out ij left right 4 4 path4 inner
  by_cases equal : E.card=4
  · exact Or.inl equal
  have five : E.card=5 := by omega
  have only (t : V) (tE : t∈E) (tW : t∉W) : t=z := by
    by_contra diff
    let N := G.neighborFinset t \ p.support.toFinset
    have inc : N ⊆ E \ W := by
      intro w hw
      obtain ⟨edge,off⟩ := mem_sdiff.mp hw
      refine mem_sdiff.mpr ⟨mem_compl.mpr off,fun wW => ?_⟩
      have bad := bd w wW t ((G.mem_neighborFinset _ _).mp edge).symm tW
      exact (mem_compl.mp tE) (List.mem_toFinset.mpr bad)
    have highT : 3 ≤ N.card := retain t diff (by simpa [E] using tE)
    have count := card_le_card inc
    rw [card_sdiff_of_subset sub] at count
    omega
  obtain ⟨t,ht⟩ := card_pos.mp (show 0 < (E \ W).card by rw [card_sdiff_of_subset sub]; omega)
  obtain ⟨tE,tW⟩ := mem_sdiff.mp ht
  obtain rfl := only t tE tW
  refine Or.inr ⟨five,by simpa [E] using tE,?_⟩
  intro w hw
  by_contra off
  have wE : w∈E := mem_compl.mpr off
  have edge := (G.mem_neighborFinset _ _).mp hw
  by_cases wW : w∈W
  · exact (mem_compl.mp tE) (List.mem_toFinset.mpr (bd w wW t edge.symm tW))
  · exact edge.ne (only w wE wW).symm

#print axioms classify
end Graph189FiveLowComponent
