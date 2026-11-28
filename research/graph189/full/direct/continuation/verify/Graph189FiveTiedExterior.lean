import Graph189FivePortOrder

open Finset SimpleGraph Graph189ExteriorGap Graph189FourExterior
namespace Graph189FiveTiedExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}

/-- With minimum degree five, at most five distance-two neighbors, and
order at most twenty, every nonspanning longest path omits exactly four vertices. -/
theorem four_omissions (p : G.Walk a b) (hp : p.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (minimum : ∀ w, 5 ≤ G.degree w) (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5)
    (limit : Fintype.card V ≤ 20) {x : V} (miss : x∉p.support) : (p.support.toFinsetᶜ : Finset V).card=4 := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card=4
  obtain ⟨W,xW,conn,out,bd⟩ := exterior_component p miss
  let H := G.induce (W : Set V)
  have raw (w : V) (off : w∉p.support) : 3 ≤ (G.neighborFinset w \ p.support.toFinset).card := by
    have v := minimum w
    have h := (high_exterior_half p hp maximal off (quota w) v
      (fun t => by have := minimum t; omega) (fun t _ th _ => by have := minimum t; omega)).2
    omega
  have deg (w : W) : 3 ≤ H.degree w := by
    change 3 ≤ (G.induce (W : Set V)).degree w
    rw [Graph189DenseExteriorOrder.component_internal_degree p W out bd]
    exact raw w (out _ w.property)
  have large : 4 ≤ W.card := by
    let x' : W := ⟨x,xW⟩
    have lower := deg x'
    have ub := H.degree_lt_card_verts x'
    change H.degree x' < Fintype.card W at ub
    rw [Fintype.card_coe] at ub
    omega
  have sub : W ⊆ E := fun t ht => by simpa [E] using out t ht
  have le := card_le_card sub
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have space : 2 ≤ p.support.length := by
    obtain ⟨y,hy⟩ := card_pos.mp (show 0 < (G.neighborFinset x).card by
      rw [G.card_neighborFinset_eq_degree]; have := minimum x; omega)
    have e := (G.mem_neighborFinset _ _).mp hy
    have bound := maximal e.toWalk e.isPath_toWalk
    rw [e.length_toWalk] at bound
    have := p.length_support
    omega
  obtain ⟨i,j,u,v,ij,ne,left,right⟩ := two_ports p hp W out bd (by omega) space cuts
  by_cases small : W.card ≤ 5
  · have routes (s t : W) (diff : s≠t) : ∃ q : H.Walk s t, q.IsPath ∧ W.card ≤ q.support.length := by
      obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top (by
        intro w y _ _
        change Fintype.card W+1 ≤ H.degree w+H.degree y
        rw [Fintype.card_coe]
        have := deg w
        have := deg y
        omega) (Graph189TerminalLeafClosure.complete_prescribed s t diff)
      exact ⟨q,hq.isPath,by rw [hq.length_support]; change W.card ≤ Fintype.card W; rw [Fintype.card_coe]⟩
    have tails (s : W) : ∃ t, ∃ q : H.Walk s t, q.IsPath ∧ W.card ≤ q.support.length := by
      by_cases eq : s=u
      · exact ⟨v,routes s v (eq ▸ ne)⟩
      · exact ⟨u,routes s u eq⟩
    have length := detour_order p hp maximal W out ij left right W.card W.card tails (routes u v ne)
    have four : W.card=4 := by omega
    by_contra diff
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (E \ W).card by rw [card_sdiff_of_subset sub]; omega)
    obtain ⟨zE,zW⟩ := mem_sdiff.mp hz
    let N := G.neighborFinset z \ p.support.toFinset
    have incl : insert z N ⊆ E \ W := by
      intro t ht
      rcases mem_insert.mp ht with rfl|member
      · exact hz
      obtain ⟨edge,off⟩ := mem_sdiff.mp member
      refine mem_sdiff.mpr ⟨mem_compl.mpr off,fun tw => ?_⟩
      have bad := bd t tw z ((G.mem_neighborFinset _ _).mp edge).symm zW
      exact (mem_compl.mp zE) (List.mem_toFinset.mpr bad)
    have bound := card_le_card incl
    have notself : z∉N := fun h => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp h).1)
    rw [card_insert_of_notMem notself,card_sdiff_of_subset sub] at bound
    have lower : 3 ≤ N.card := raw z (by simpa [E] using zE)
    omega
  have near : ∃ q : H.Walk u v, q.IsPath ∧ 2 ≤ q.support.length := by
    obtain ⟨q,hq⟩ := conn.exists_isPath u v
    have nz : q.length≠0 := fun h => ne (Walk.exists_length_eq_zero_iff.mp ⟨q,h⟩)
    exact ⟨q,hq,by have := q.length_support; omega⟩
  let Good (w : W) := ∃ t, ∃ q : H.Walk w t, q.IsPath ∧ 5 ≤ q.support.length
  have other (s t : W) (st : s≠t) (bad : ¬Good s) : 7 ≤ W.card ∧ Good t := by
    obtain ⟨all,size⟩ := Graph189FiveExteriorRoots.deficient H conn deg s bad
    change Fintype.card W=4 ∨ 7 ≤ Fintype.card W at size
    rw [Fintype.card_coe] at size
    refine ⟨by omega,?_⟩
    by_contra second
    obtain ⟨univT,_⟩ := Graph189FiveExteriorRoots.deficient H conn deg t second
    have nb : H.neighborFinset t=univ.erase t := by
      ext w
      simp only [H.mem_neighborFinset,mem_erase,mem_univ,and_true]
      exact ⟨fun e => e.ne.symm,fun h => (univT w h).1⟩
    have nc := congrArg Finset.card nb
    rw [H.card_neighborFinset_eq_degree,card_erase_of_mem (mem_univ t),card_univ,Fintype.card_coe] at nc
    have th := (all t st.symm).2
    omega
  have far (bound : W.card ≤ 7) := Graph189FivePortOrder.three_between H
    (by change Fintype.card W ≤ 7; rwa [Fintype.card_coe]) deg u v ne
  have rooted := Graph189FiveExteriorRoots.four_from H deg
  by_cases first : Good u
  · by_cases second : Good v
    · have len := Graph189FivePortOrder.order p hp maximal W out ij left right 5 5 2 first second near
      have more := Graph189FivePortOrder.order p hp maximal W out ij left right 5 5 3 first second (far (by omega))
      omega
    · have bs := (other v u ne.symm second).1
      have len := Graph189FivePortOrder.order p hp maximal W out ij left right 5 4 2 first (rooted v) near
      have more := Graph189FivePortOrder.order p hp maximal W out ij left right 5 4 3 first (rooted v) (far (by omega))
      omega
  · obtain ⟨bs,second⟩ := other u v ne first
    have len := Graph189FivePortOrder.order p hp maximal W out ij left right 4 5 2 (rooted u) second near
    have more := Graph189FivePortOrder.order p hp maximal W out ij left right 4 5 3 (rooted u) second (far (by omega))
    omega

#print axioms four_omissions
end Graph189FiveTiedExterior
