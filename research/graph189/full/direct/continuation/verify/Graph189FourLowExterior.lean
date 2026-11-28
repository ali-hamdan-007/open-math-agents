import Graph189FourExterior

open Finset SimpleGraph Graph189ExteriorGap Graph189FourExterior
namespace Graph189FourLowExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- A component containing an omitted high vertex has enough internal paths
to force exactly three omissions when the unique low degree is two or three. -/
theorem three_omitted (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (zdeg : G.degree z=2 ∨ G.degree z=3)
    (high : ∀ w, w≠z → 4 ≤ G.degree w)
    (raw : ∀ w, w≠z → w∉p.support → 2 ≤ (G.neighborFinset w \ p.support.toFinset).card)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ 4)
    (order : Fintype.card V ≤ 11+G.degree z) {v : V} (vz : v≠z) (off : v∉p.support) :
    (p.support.toFinsetᶜ : Finset V).card=3 := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=3
  obtain ⟨W,vW,conn,out,bd⟩ := exterior_component p off
  let H := G.induce (W : Set V)
  have d (w : W) (wz : w.val≠z) : 2 ≤ H.degree w := by
    change 2 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact raw w.val wz (out w.val w.property)
  have large : 3 ≤ W.card := by
    let w : W := ⟨v,vW⟩
    have dl := d w vz
    have bound := H.degree_lt_card_verts w
    change H.degree w < Fintype.card W at bound
    rw [Fintype.card_coe] at bound
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe]; omega)
  have highNeighbor (w : W) : ∃ y : W, H.Adj w y ∧ y.val≠z := by
    by_cases lo : w.val=z
    · obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (H.neighborFinset w).card from conn.preconnected.degree_pos_of_nontrivial w)
      have e := (H.mem_neighborFinset _ _).mp hy
      exact ⟨y,e,fun h => e.ne (Subtype.ext (lo.trans h.symm))⟩
    · obtain ⟨u,hu,y,hy,uy⟩ := one_lt_card.mp (show 1 < (H.neighborFinset w).card from d w lo)
      by_cases uz : u.val=z
      · exact ⟨y,(H.mem_neighborFinset _ _).mp hy,fun e => uy (Subtype.ext (uz.trans e.symm))⟩
      · exact ⟨u,(H.mem_neighborFinset _ _).mp hu,uz⟩
  have tails (w : W) : ∃ y, ∃ q : H.Walk w y, q.IsPath ∧ 3 ≤ q.support.length := by
    obtain ⟨y,wy,yz⟩ := highNeighbor w
    obtain ⟨u,hu,uw⟩ := exists_mem_ne (show 1 < (H.neighborFinset y).card from d y yz) w
    have yu := (H.mem_neighborFinset _ _).mp hu
    let q : H.Walk w u := .cons wy (.cons yu .nil)
    exact ⟨u,q,Walk.IsPath.mk' (by simp [q,wy.ne,yu.ne,uw.symm]),by simp [q]⟩
  have space : 2 ≤ p.support.length := by
    let w : W := ⟨v,vW⟩
    obtain ⟨y,wy,_⟩ := highNeighbor w
    have e : G.Adj v y.val := wy
    have len := maximal e.toWalk e.isPath_toWalk
    rw [e.length_toWalk] at len
    have := p.length_support
    omega
  obtain ⟨i,j,u,w,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  have route : ∃ q : H.Walk u w, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u w
    have nonzero : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  have base := detour_order p hp maximal W out ij left right 3 2 tails route
  have count := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at count
  change p.support.length+E.card=Fintype.card V at count
  have ws := card_le_card (show W ⊆ E from fun t ht => by simpa [E] using out t ht)
  rcases zdeg with two|three
  · omega
  have all (w : W) : 2 ≤ H.degree w := by
    by_cases wz : w.val=z
    · obtain ⟨y,e,yz⟩ := highNeighbor w
      have h := half_degree_outside_longest p hp maximal (out w.val w.property) (out y.val y.property)
        (show G.Adj w.val y.val from e) (quota w.val) (high y.val yz)
      change 2 ≤ (G.induce (W : Set V)).degree w
      rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
      rw [wz,three] at h
      rw [wz]
      omega
    · exact d w wz
  have small : Fintype.card W ≤ 5 := by rw [Fintype.card_coe]; omega
  have longer := Graph189FourRoutes.three_between H small all u w ne
  have stronger := detour_order p hp maximal W out ij left right 3 3 tails longer
  omega

#print axioms three_omitted
end Graph189FourLowExterior
