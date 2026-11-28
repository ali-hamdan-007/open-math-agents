import Graph189OptimalNeighborhood
import Graph189PrescribedBatch
import Graph189ExteriorPopulation

open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189OptimalExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Deleting the possible low vertex from the closed internal neighborhood leaves
a Hamilton-connected core. A low vertex lost here cannot also cause an overlap
between shifted path marks. -/
theorem high_core {a b : V} {p : G.Walk a b} {C : Finset V} {k : ℕ} (h : Chosen p C k)
    {x : V} (xc : x∈C) (high : k≤G.degree x)
    (noncut : (G.induce (C.erase x:Set V)).Preconnected)
    (minimum : ∀v,3≤G.degree v) (uniqueLow : ∀u v,G.degree u<k → G.degree v<k → u=v)
    (quota : (univ.filter (fun v => G.dist x v=2)).card≤k)
    (dense : 3*(G.neighborFinset x∩C).card+3≤2*k) :
    let N := G.neighborFinset x∩C
    let X := insert x N
    let H := X.filter (fun y => k≤G.degree y)
    let R := C.filter (fun y => G.dist x y=2)
    N.card≤H.card ∧ H⊆C ∧ R.card+k+(X \ H).card≤2*N.card+1 ∧
      (∀y∈H,k≤(contactPositions p y).card+N.card+R.card) ∧
      ∀u v : H,u≠v → ∃q : (G.induce (H:Set V)).Walk u v,q.IsHamiltonian := by
  classical
  let N := G.neighborFinset x∩C
  let X := insert x N
  let H := X.filter (fun y => k≤G.degree y)
  let R := C.filter (fun y => G.dist x y=2)
  let D := X \ H
  let L := p.support.toFinset.filter (fun y => G.degree y<k)
  have Xsub : X⊆C := insert_subset xc (inter_subset_right)
  have inX : x∉N := fun m => G.irrefl ((G.mem_neighborFinset _ _).mp (mem_inter.mp m).1)
  have size : X.card=N.card+1 := card_insert_of_notMem inX
  have e := card_sdiff_add_card_eq_card (show H⊆X from filter_subset _ _)
  change D.card+H.card=X.card at e
  have lowD {y : V} (yd : y∈D) : G.degree y<k := by
    by_contra! hy
    exact (mem_sdiff.mp yd).2 (mem_filter.mpr ⟨(mem_sdiff.mp yd).1,hy⟩)
  have lows : (D∪L).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    have low {y : V} (hy : y∈D∪L) : G.degree y<k :=
      (mem_union.mp hy).elim lowD (fun m => (mem_filter.mp m).2)
    exact uniqueLow _ _ (low hu) (low hv)
  have apart : Disjoint D L := Finset.disjoint_left.mpr (fun _ yd yp =>
    h.outside _ (Xsub (mem_sdiff.mp yd).1) (List.mem_toFinset.mp (mem_filter.mp yp).1))
  rw [card_union_of_disjoint apart] at lows
  obtain ⟨radius,neighbors⟩ := local_bounds h xc high noncut minimum uniqueLow quota
  change R.card+k≤2*N.card+L.card at radius
  change N.card≤H.card ∧ H⊆C ∧ R.card+k+D.card≤2*N.card+1 ∧ _
  refine ⟨by omega,(filter_subset _ _).trans Xsub,by omega,?_,?_⟩
  · intro y hy
    exact (neighbors y (mem_filter.mp hy).1 (mem_filter.mp hy).2).2
  let J := G.induce (H:Set V)
  have density (v : H) : k ≤ J.degree v + N.card + D.card := by
    have localDegree := (neighbors v.val (mem_filter.mp v.property).1 (mem_filter.mp v.property).2).1
    change k≤(G.neighborFinset v.val∩X).card+N.card at localDegree
    have cover : G.neighborFinset v.val∩X⊆(G.neighborFinset v.val∩H)∪D := by
      intro y hy
      by_cases m : y∈H
      · exact mem_union_left _ (mem_inter.mpr ⟨(mem_inter.mp hy).1,m⟩)
      exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_inter.mp hy).2,m⟩)
    have bound := (card_le_card cover).trans (card_union_le _ _)
    have graph : J.degree v=(G.neighborFinset v.val∩H).card := by
      rw [show J.degree v=_ from Graph189ExteriorDegreeCycle.degree_induce_filter (H:Set V) v]
      congr 1
    rw [graph]
    omega
  intro u v diff
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=J) le_top _
    (Graph189TerminalLeafClosure.complete_prescribed u v diff)
  intro i j _ _
  change Fintype.card H+1≤J.degree i+J.degree j
  rw [Fintype.card_coe]
  change 3*N.card+3≤2*k at dense
  have di := density i
  have dj := density j
  omega

end Graph189OptimalExterior
#print axioms Graph189OptimalExterior.high_core
