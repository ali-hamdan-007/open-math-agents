import Graph189FiveCycleContacts
import Graph189LayerCover

open Finset SimpleGraph Graph189ExteriorGap
namespace Graph189FiveExteriorData
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}

/-- For five omissions a matching cap of two identifies their clique,
the two contacts of every high row, and the ambient bound 23. -/
theorem window (p : G.Walk a b) (E : Finset V)
    (boundary : ∀ u∈E, ∀ v, G.Adj u v → v∉E → v∈p.support) (hc : G.Connected) (six : G.secondSmallestDegree=6)
    (cap : ∀ v, G.distEven v≤7) (five : E.card=5)
    (limit : ∀ M : Finset (Fin p.support.length), M.card=3 → ∀ f : M↪E,
      (∀ i : M, G.Adj p.support[i.val.val] (f i).val) → False) :
    ∃ M : Finset (Fin p.support.length), M.card=2 ∧
      (∀ v∈E, 6≤G.degree v → ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈M) ∧
      (∀ v∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] v → i∈M) ∧
      G.IsClique (E : Set V) ∧ Fintype.card V≤23 := by
  classical
  let D := E.filter (fun v => 6≤G.degree v)
  have sub : D⊆E := filter_subset _ _
  change E.card=5 at five
  have one : (E\D).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have h := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    rcases h with h|h
    · exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,by omega⟩)
    · exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,by omega⟩)
  have many : 3≤D.card := by have n := card_sdiff_add_card_eq_card sub; omega
  let row (v : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] v)
  have supported (v : V) (vd : v∈D) :
      insert v (G.neighborFinset v)⊆E∪(row v).image (fun i => p.support[i.val]) := by
    intro u hu
    rcases mem_insert.mp hu with rfl|eu
    · exact mem_union_left _ (sub vd)
    by_cases ue : u∈E
    · exact mem_union_left _ ue
    have on : u∈p.support := boundary v (sub vd) u ((G.mem_neighborFinset _ _).mp eu) ue
    obtain ⟨i,hi,value⟩ := List.mem_iff_getElem.mp on
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,mem_filter.mpr ⟨mem_univ _,by
      change G.Adj p.support[i] v
      rw [value]
      exact ((G.mem_neighborFinset _ _).mp eu).symm⟩,value⟩)
  have rows (v : V) (vd : v∈D) : 2≤(row v).card := by
    have h := (card_le_card (supported v vd)).trans (card_union_le _ _)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree,five] at h
    have bound : ((row v).image (fun i => p.support[i.val])).card≤(row v).card := card_image_le
    have hi := (mem_filter.mp vd).2
    omega
  obtain ⟨M,two,full,all⟩ := Graph189FiveCycleContacts.pair p E D sub many rows limit
  let P := M.image (fun i => p.support[i.val])
  have small : P.card≤2 := card_image_le.trans two.le
  have marked {u v : V} (ue : u∈E) (touch : G.Adj u v) (vp : v∈p.support) : v∈P := by
    obtain ⟨i,hi,value⟩ := List.mem_iff_getElem.mp vp
    exact mem_image.mpr ⟨⟨i,hi⟩,all u ue ⟨i,hi⟩ (by change G.Adj p.support[i] u; rw [value]; exact touch.symm),value⟩
  have exactN {u : V} (ud : u∈D) : G.neighborFinset u=E.erase u∪P := by
    have inc : G.neighborFinset u⊆E.erase u∪P := by
      intro v hv
      have e := (G.mem_neighborFinset _ _).mp hv
      by_cases ve : v∈E
      · exact mem_union_left _ (mem_erase.mpr ⟨e.ne.symm,ve⟩)
      exact mem_union_right _ (marked (sub ud) e (boundary u (sub ud) v e ve))
    apply eq_of_subset_of_card_le inc
    have h := card_union_le (E.erase u) P
    rw [card_erase_of_mem (sub ud),five] at h
    rw [G.card_neighborFinset_eq_degree]
    have high := (mem_filter.mp ud).2
    omega
  have sees {u v : V} (ud : u∈D) (ve : v∈E) (uv : u≠v) : G.Adj u v := by
    apply (G.mem_neighborFinset _ _).mp
    rw [exactN ud]
    exact mem_union_left _ (mem_erase.mpr ⟨uv.symm,ve⟩)
  have clique : G.IsClique (E : Set V) := by
    intro u ue v ve ne
    by_cases ud : u∈D
    · exact sees ud ve ne
    by_cases vd : v∈D
    · exact (sees vd ue ne.symm).symm
    exact False.elim (ne (card_le_one.mp one u (mem_sdiff.mpr ⟨ue,ud⟩) v (mem_sdiff.mpr ⟨ve,vd⟩)))
  obtain ⟨x,xd⟩ := card_pos.mp (show 0<D.card by omega)
  have arms (v : V) (vp : v∈P) : G.Adj x v := by
    apply (G.mem_neighborFinset _ _).mp
    rw [exactN xd]
    exact mem_union_right _ vp
  have cover (v : V) (layer : v∈Graph189LayerCover.layer G x 2) : ∃ u∈P,G.Adj u v := by
    have d := Graph189LayerCover.in_layer.mp layer
    have ed : G.edist x v=2 := by rw [←(hc x v).coe_dist_eq_edist,d]; rfl
    obtain ⟨different,missing,u,adj⟩ := edist_eq_two_iff.mp ed
    obtain ⟨xu,vu⟩ := G.mem_commonNeighbors.mp adj
    have pos := (G.mem_neighborFinset _ _).mpr xu
    rw [exactN xd] at pos
    rcases mem_union.mp pos with ue|up
    · have ve : v∉E := fun h => missing (sees xd h different)
      have vp : v∈p.support := boundary u (mem_erase.mp ue).2 v vu.symm ve
      obtain ⟨i,hi,value⟩ := List.mem_iff_getElem.mp vp
      have im := all u (mem_erase.mp ue).2 ⟨i,hi⟩ (by change G.Adj p.support[i] u; rw [value]; exact vu)
      exact False.elim (missing (arms v (mem_image.mpr ⟨⟨i,hi⟩,im,value⟩)))
    · exact ⟨u,up,vu.symm⟩
  have dx : G.degree x≤6 := by
    rw [←G.card_neighborFinset_eq_degree,exactN xd]
    have h := card_union_le (E.erase x) P
    rw [card_erase_of_mem (sub xd),five] at h
    omega
  obtain ⟨n,smallN,_,bd⟩ := Graph189LayerCover.order_of_cover G hc x 6 cap P arms cover
  have result : Fintype.card V≤23 := by
    have cases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases cases with rfl|rfl|rfl <;> omega
  exact ⟨M,two,fun v ve high => full v (mem_filter.mpr ⟨ve,high⟩),all,clique,result⟩

theorem data (p : G.Walk a b) (hc : G.Connected) (six : G.secondSmallestDegree=6)
    (cap : ∀ v, G.distEven v≤7) (five : p.support.toFinsetᶜ.card=5)
    (limit : ∀ M : Finset (Fin p.support.length), M.card=3 → ∀ f : M↪(p.support.toFinsetᶜ : Finset V),
      (∀ i : M, G.Adj p.support[i.val.val] (f i).val) → False) :
    let E := p.support.toFinsetᶜ
    ∃ M : Finset (Fin p.support.length), M.card=2 ∧
      (∀ v∈E, 6≤G.degree v → ∀ i : Fin p.support.length, G.Adj p.support[i.val] v ↔ i∈M) ∧
      (∀ v∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] v → i∈M) ∧
      G.IsClique (E : Set V) ∧ Fintype.card V≤23 := by
  exact window p p.support.toFinsetᶜ (fun _ _ _ _ outside => by simpa using outside) hc six cap five limit

#print axioms window
#print axioms data
end Graph189FiveExteriorData
