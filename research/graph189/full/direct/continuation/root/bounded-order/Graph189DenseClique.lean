import Graph189DenseCommonContacts
import Graph189MinimumCut

open SimpleGraph Finset Graph189OptimalExterior Graph189ExteriorGap
namespace Graph189ExteriorLeaf
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The paper's saturated clique and its common marks, with the possible low
vertex allowed to miss marks. Every other omitted vertex is the unique low. -/
structure Saturated {a b : V} (p : G.Walk a b) (C : Finset V) (k : ℕ) : Prop where
  small : C.card+2≤k
  spare : p.support.toFinsetᶜ.card≤C.card+1
  clique : G.IsClique (C:Set V)
  marks : ∃A : Finset (Fin p.support.length), A.card=k+1-C.card ∧
    (∀v∈C,k≤G.degree v → ∀i : Fin p.support.length,G.Adj p.support[i.val] v ↔ i∈A) ∧
    ∀v∈C,∀i : Fin p.support.length,G.Adj p.support[i.val] v → i∈A

theorem dense_clique_of_size {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (dense : ∀v∈C,k≤G.degree v → C.card+1≤2*(G.neighborFinset v∩C).card)
    (lo : 7≤k) (upper : Fintype.card V≤5*k-5) (small : C.card+2≤k)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (gap : p.support.length+(k+1)/2+1<Fintype.card V) : Saturated p C k := by
  classical
  obtain ⟨r⟩ := dense_component_routes h lo quota minimum uniqueLow dense
  obtain ⟨many,_,low,_,upperM⟩ := dense_exterior_census h r small lo upper quota minimum uniqueLow gap
  let H := C.filter (fun v => k≤G.degree v)
  let E := p.support.toFinsetᶜ
  let s := k+1-C.card
  have subE : C⊆E := fun v vc => mem_compl.mpr (fun on => h.outside _ vc (List.mem_toFinset.mp on))
  have spare : (E \ C).card≤1 := card_le_one_iff.mpr (by
    intro u v hu hv
    exact uniqueLow _ _ (low u (mem_sdiff.mp hu).1 (mem_sdiff.mp hu).2) (low v (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2))
  have total := card_sdiff_add_card_eq_card subE
  have rows (v : V) (vh : v∈H) : s≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] v)).card := by
    have bound := Graph189DenseExteriorOrder.neighbors_on_path p C
      (fun u uc y e out => by by_contra miss; exact out (h.closed u uc y e miss)) (mem_filter.mp vh).1
    have high := (mem_filter.mp vh).2
    dsimp [s]; omega
  obtain ⟨A,count,links,cover⟩ := common_contacts h r (s:=s) (by dsimp [s]; omega) H
    (filter_subset _ _) many rows upperM
  refine ⟨small,by change E.card≤C.card+1; omega,?_,
    ⟨A,count,fun v vc high => links v (mem_filter.mpr ⟨vc,high⟩),cover⟩⟩
  let B := A.image (fun i : Fin p.support.length => p.support[i.val])
  have bsize : B.card≤s := card_image_le.trans count.le
  have universal (u : V) (uc : u∈C) (high : k≤G.degree u) (v : V) (vc : v∈C) (ne : u≠v) : G.Adj u v := by
    let W := C.erase u ∪ B
    have sub : G.neighborFinset u⊆W := by
      intro z hz
      have edge := (G.mem_neighborFinset _ _).mp hz
      by_cases zc : z∈C
      · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,zc⟩)
      have on : z∈p.support := by by_contra miss; exact zc (h.closed u uc z edge miss)
      obtain ⟨i,valid,eq⟩ := List.mem_iff_getElem.mp on
      let j : Fin p.support.length := ⟨i,valid⟩
      have marked := cover u uc j (by simpa [j,eq] using edge.symm)
      exact mem_union_right _ (mem_image.mpr ⟨j,marked,eq⟩)
    have union := card_union_le (C.erase u) B
    have er := card_erase_add_one uc
    have du := G.card_neighborFinset_eq_degree u
    have size : W.card≤G.degree u := by
      change W.card≤_ at union
      dsimp [s] at bsize
      omega
    have eq := eq_of_subset_of_card_le sub (size.trans_eq du.symm)
    exact (G.mem_neighborFinset _ _).mp (eq ▸ mem_union_left _ (mem_erase.mpr ⟨ne.symm,vc⟩))
  intro u uc v vc ne
  by_cases hu : k≤G.degree u
  · exact universal u uc hu v vc ne
  have hv : k≤G.degree v := by by_contra! miss; exact ne (uniqueLow _ _ (by omega) miss)
  exact (universal v vc hv u uc ne.symm).symm

theorem dense_clique {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    (dense : ∀v∈C,k≤G.degree v → C.card+1≤2*(G.neighborFinset v∩C).card)
    (lo : 7≤k) (upper : Fintype.card V≤5*k-5) (conn : 3≤G.vertexConnectivity)
    (quota : ∀v,(univ.filter (fun z => G.dist v z=2)).card≤k)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (gap : p.support.length+(k+1)/2+1<Fintype.card V) : Saturated p C k := by
  obtain ⟨x,xc,xh⟩ := h.high
  have half := xh.trans (internal_half h xc xh (quota _) minimum uniqueLow)
  have deg := card_le_card (inter_subset_right (s₁:=G.neighborFinset x) (s₂:=C))
  obtain ⟨r⟩ := dense_component_routes h lo quota minimum uniqueLow dense
  have small := dense_component_size h r (by omega) upper lo (fun cut lt =>
    Graph189CutSides.connected_after_smaller_deletion cut (by omega))
  exact dense_clique_of_size h dense lo upper small quota minimum uniqueLow gap

end Graph189ExteriorLeaf
#print axioms Graph189ExteriorLeaf.dense_clique
