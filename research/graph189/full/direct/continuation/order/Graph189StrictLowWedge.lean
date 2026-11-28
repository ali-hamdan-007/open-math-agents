import Graph189WedgeOrder

open Finset SimpleGraph
namespace Graph189WedgeOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A second common neighbor of higher degree forces a unit of strict slack
in the three-root incidence bound. -/
theorem strict_order (hc : G.Connected) {x y z i : V} (xy : G.Adj x y) (xz : G.Adj x z)
    (yz : ¬G.Adj y z) (yi : G.Adj y i) (zi : G.Adj z i) (high : G.degree x<G.degree i)
    {k : ℕ} (cap : ∀v,G.distEven v≤k+1) :
    Fintype.card V+(k+1)*(G.neighborFinset x∪(G.neighborFinset y∪G.neighborFinset z)).card <
      3*k+2+k*(G.degree x+G.distEven x)+G.degree y+G.degree z := by
  classical
  let N := G.neighborFinset x
  let C := G.neighborFinset y∩G.neighborFinset z
  let I := C∩N
  let E (a : V) := univ.filter (fun v => Even (G.dist a v))
  let O := (E y∪E z)∩E x
  have incX : x∈C := mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr xy.symm,(G.mem_neighborFinset _ _).mpr xz.symm⟩
  have noX : x∉I := fun h => G.irrefl ((G.mem_neighborFinset x x).mp (mem_inter.mp h).2)
  have cover : insert x I⊆C := insert_subset incX inter_subset_left
  have base := wedge_order_with_overlap hc xy xz yz cap
  change Fintype.card V+_+(C.card-(I.card+1))+O.card≤_ at base
  by_cases large : I.card+2≤C.card
  · omega
  have cnt := card_insert_of_notMem noX
  have eq : insert x I=C := eq_of_subset_of_card_le cover (by omega)
  have inside {a : V} (h : a∈C) (other : a≠x) : a∈N := by
    rw [←eq] at h
    exact (mem_inter.mp ((mem_insert.mp h).resolve_left other)).2
  have ix : i≠x := fun e => (Nat.lt_irrefl _ (e ▸ high))
  have iN := inside (mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr yi,(G.mem_neighborFinset _ _).mpr zi⟩) ix
  obtain ⟨v,iv,vn,vx⟩ : ∃ v,G.Adj i v ∧ v∉N ∧ v≠x := by
    by_contra! fail
    have inc : G.neighborFinset i⊆insert x (N.erase i) := by
      intro v hv
      have edge := (G.mem_neighborFinset _ _).mp hv
      by_cases vn : v∈N
      · exact mem_insert_of_mem (mem_erase.mpr ⟨edge.ne.symm,vn⟩)
      exact mem_insert.mpr (Or.inl (fail v edge vn))
    have count := (card_le_card inc).trans (card_insert_le _ _)
    have er := card_erase_add_one iN
    change (N.erase i).card+1=(G.neighborFinset x).card at er
    rw [G.card_neighborFinset_eq_degree] at count er
    omega
  have notC : v∉C := fun h => vn (inside h vx)
  have even2 {a : V} (ai : G.Adj a i) (av : ¬G.Adj a v) : v∈E a := by
    have d := hc.dist_triangle (u:=a) (v:=i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr ai,dist_eq_one_iff_adj.mpr iv] at d
    have not1 : G.dist a v≠1 := fun eq => av (dist_eq_one_iff_adj.mp eq)
    exact mem_filter.mpr ⟨mem_univ _,by rw [Nat.even_iff]; omega⟩
  have ex := even2 ((G.mem_neighborFinset _ _).mp iN) (fun edge => vn ((G.mem_neighborFinset _ _).mpr edge))
  have ez : v∈E y∪E z := by
    by_cases a : G.Adj y v
    · exact mem_union_right _ (even2 zi (fun b => notC (mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr a,(G.mem_neighborFinset _ _).mpr b⟩)))
    exact mem_union_left _ (even2 yi a)
  have pos : 0<O.card := card_pos.mpr ⟨v,mem_inter.mpr ⟨ez,ex⟩⟩
  omega

#print axioms strict_order
end Graph189WedgeOrder
