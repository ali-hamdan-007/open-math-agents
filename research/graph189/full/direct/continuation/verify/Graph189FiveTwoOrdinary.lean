import Graph189FiveLeafNeighbors
import Graph189FiveLowMarks
import Graph189RootedOneLow
import Graph189FourExterior
import Graph189ThreeOriginal

open SimpleGraph Finset Graph189ExteriorGap Graph189FourExterior
namespace Graph189FiveTwoOrdinary
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph with the degree-two exception at second degree five either admits
a Hamilton path or has one after deletion of its degree-two vertex. -/
theorem traceable_or_deletion
    (cuts : ∀ U : Finset V, U.card<2 → (G.induce {v : V | v∉U}).Connected)
    (z : V) (degree : G.degree z=2) (high : ∀ w, w≠z → 5 ≤ G.degree w)
    (quota : ∀ w, (univ.filter (fun t => G.dist w t=2)).card ≤ 5) (limit : Fintype.card V ≤ 16) :
    (∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian) ∨
      (∃ c d, ∃ q : (G.induce {v : V | v≠z}).Walk c d, q.IsHamiltonian) := by
  classical
  obtain ⟨a,b,p,hp,maximal⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := (p.support.toFinsetᶜ : Finset V)
  have retain (w : V) (wz : w≠z) (off : w∉p.support) :=
    Graph189FiveLeafNeighbors.three p hp maximal z degree high quota limit wz off
  have every (x : V) (xz : x≠z) : x∈p.support := by
    by_contra miss
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
    have sz : E.card=4 := by omega
    have eq : W=E := eq_of_subset_of_card_le sub (by omega)
    obtain ⟨routes,_,_,_⟩ := Graph189FiveLowMarks.data p hp maximal z high retain (by omega) sz
    have spanning : ∀ s t : W, s≠t → ∃ q : (G.induce (W : Set V)).Walk s t, q.IsHamiltonian := by
      rw [eq]
      exact routes
    obtain ⟨q,hq⟩ := spanning u v ne
    have inner : ∃ q : H.Walk u v, q.IsPath ∧ 4 ≤ q.support.length := by
      refine ⟨q,hq.isPath,?_⟩
      rw [hq.length_support]
      change 4 ≤ Fintype.card W
      rwa [Fintype.card_coe]
    have longer := detour_order p hp maximal W out ij left right 4 4 path4 inner
    omega
  by_cases on : z∈p.support
  · exact Or.inl ⟨a,b,p,hp.isHamiltonian_of_mem (fun w => by
      by_cases e : w=z
      · exact e ▸ on
      · exact every w e)⟩
  let S := {w : V | w≠z}
  have sub : ∀ w∈p.support, w∈S := fun w hw e => on (e ▸ hw)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapped : q.map f=p := Walk.map_induce p sub
  have path : q.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  apply Or.inr ⟨_,_,q,path.isHamiltonian_of_mem ?_⟩
  intro w
  have belongs := every w.val w.property
  have supp : List.map Subtype.val q.support=p.support := by
    calc
      List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
      _ = p.support := congrArg (fun r : G.Walk a b => r.support) mapped
  rw [←supp] at belongs
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp belongs
  exact (Subtype.ext eq : t=w) ▸ ht

#print axioms traceable_or_deletion
end Graph189FiveTwoOrdinary
