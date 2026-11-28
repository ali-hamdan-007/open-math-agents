import Graph189GraphPopulation
import Graph189ThreeLargeComponents

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189TwoCutSelect
open Finset SimpleGraph Graph189CutSides
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- Choose the smallest side across all genuine size-two separators. This
form of the minimum immediately applies to the new cut in the recut proof. -/
theorem exists_least_cut (conn : G.vertexConnectivity=2)
    (room : G.vertexConnectivity<Fintype.card V-1) :
    ∃ A B : Finset V, ∃ p q : V, p≠q ∧ CutSides G A B {p,q} ∧
      ∀ C D T, CutSides G C D T → T.card=2 → A.card≤C.card := by
  classical
  obtain ⟨C,D,T,ts,cd⟩ := Graph189GraphPopulation.minimum_sides (G:=G) room
  let Sizes (n : ℕ) := ∃ C D T : Finset V, CutSides G C D T ∧ T.card=2 ∧ C.card=n
  have sizes : ∃ n, Sizes n := ⟨C.card,C,D,T,cd,ts.trans conn,rfl⟩
  obtain ⟨A,B,S,cut,sc,least⟩ := Nat.find_spec sizes
  obtain ⟨p,q,diff,form⟩ := Finset.card_eq_two.mp sc
  refine ⟨A,B,p,q,diff,form ▸ cut,?_⟩
  intro C D T sides two
  rw [least]
  exact Nat.find_min' sizes ⟨C,D,T,sides,two,rfl⟩

omit [Nontrivial V] in
private theorem sector_size (S X : Finset V) (sc : S.card=2) (hx : X.Nonempty)
    (closed : ∀ x∈X, ∀ y, G.Adj x y → y∉X → y∈S)
    (minimum : 3≤G.minDegree) : 2≤X.card := by
  classical
  obtain ⟨x,xx⟩ := hx
  have sub : G.neighborFinset x⊆S∪X.erase x := by
    intro y yn
    have adj := (G.mem_neighborFinset _ _).mp yn
    by_cases yx : y∈X
    · exact mem_union_right _ (mem_erase.mpr ⟨adj.ne.symm,yx⟩)
    · exact mem_union_left _ (closed x xx y adj yx)
  have size := (card_le_card sub).trans (card_union_le S (X.erase x))
  rw [G.card_neighborFinset_eq_degree] at size
  have degree := minimum.trans (G.minDegree_le_degree x)
  have erase := card_erase_add_one xx
  omega

/-- A disconnected side would split into two anticomplete sectors, which
together with the opposite side contradicts the existing three-sector count. -/
theorem connected_side {A B S : Finset V} (sides : CutSides G A B S)
    (size : S.card=2) (minimumCut : S.card=G.vertexConnectivity)
    (minimum : 3≤G.minDegree) (large : 7≤G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1) :
    (G.induce (A : Set V)).Connected := by
  classical
  by_contra bad
  let H := G.induce (A : Set V)
  obtain ⟨a,aa⟩ := sides.left_nonempty
  let x : (A : Set V) := ⟨a,aa⟩
  obtain ⟨y,far⟩ : ∃ y : (A : Set V), ¬H.Reachable x y := by
    by_contra! all
    exact bad (H.connected_iff_exists_forall_reachable.mpr ⟨x,all⟩)
  let X := A.filter (fun v => ∃ hv : v∈(A:Set V), H.Reachable x ⟨v,hv⟩)
  let Y := A.filter (fun v => v∉X)
  have nx : X.Nonempty := ⟨a,mem_filter.mpr ⟨aa,⟨aa,Reachable.refl x⟩⟩⟩
  have ny : Y.Nonempty := ⟨y.val,mem_filter.mpr ⟨y.property,fun h =>
    far (mem_filter.mp h).2.choose_spec⟩⟩
  have noXY : ∀ u∈X, ∀ v∈Y, ¬G.Adj u v := by
    intro u hu v hv e
    obtain ⟨_,uh,conn⟩ := mem_filter.mp hu
    obtain ⟨va,vx⟩ := mem_filter.mp hv
    have adj : H.Adj ⟨u,uh⟩ ⟨v,va⟩ := e
    exact vx (mem_filter.mpr ⟨va,va,conn.trans adj.reachable⟩)
  have xA : X⊆A := filter_subset _ _
  have yA : Y⊆A := filter_subset _ _
  have xy : Disjoint X Y := Finset.disjoint_left.mpr (fun _ hx hy => (mem_filter.mp hy).2 hx)
  have closedX : ∀ u∈X, ∀ v, G.Adj u v → v∉X → v∈S := by
    intro u hu v e nv
    rcases sides.cover v with va|vb|vs
    · exact (noXY u hu v (mem_filter.mpr ⟨va,nv⟩) e).elim
    · exact (sides.no_cross u (xA hu) v vb e).elim
    · exact vs
  have closedY : ∀ u∈Y, ∀ v, G.Adj u v → v∉Y → v∈S := by
    intro u hu v e nv
    rcases sides.cover v with va|vb|vs
    · by_cases vx : v∈X
      · exact (noXY v vx u hu e.symm).elim
      · exact (nv (mem_filter.mpr ⟨va,vx⟩)).elim
    · exact (sides.no_cross u (yA hu) v vb e).elim
    · exact vs
  have closedB : ∀ u∈B, ∀ v, G.Adj u v → v∉B → v∈S := by
    intro u hu v e nv
    rcases sides.cover v with va|vb|vs
    · exact (sides.no_cross v va u hu e.symm).elim
    · exact (nv vb).elim
    · exact vs
  let W (i : Fin 3) := if i=0 then X else if i=1 then Y else B
  have wb : ∀ i, S.card≤(W i).card := by
    intro i
    rw [size]
    fin_cases i
    · exact sector_size S X size nx closedX minimum
    · exact sector_size S Y size ny closedY minimum
    · exact sector_size S B size sides.right_nonempty closedB minimum
  have apart : ∀ i, Disjoint S (W i) := by
    intro i
    fin_cases i
    · exact sides.left_cut.symm.mono_right xA
    · exact sides.left_cut.symm.mono_right yA
    · exact sides.right_cut.symm
  have xb : Disjoint X B := sides.apart.mono_left xA
  have yb : Disjoint Y B := sides.apart.mono_left yA
  have disj : ∀ i j, i≠j → Disjoint (W i) (W j) := by
    intro i j ne
    fin_cases i <;> fin_cases j <;> simp [W,xy,xy.symm,xb,xb.symm,yb,yb.symm] at ne ⊢
  have closed : ∀ i, ∀ u∈W i, ∀ v, G.Adj u v → v∉W i → v∈S := by
    intro i
    fin_cases i
    · exact closedX
    · exact closedY
    · exact closedB
  have bound := Graph189ThreeLargeComponents.three_sides S W (by omega) minimumCut.le
    wb disj apart closed cap
  omega

/-- A minimum component choice for the separating-pair proof, with both
sides connected and enough surviving vertices in each. -/
theorem exists_connected_least_cut (conn : G.vertexConnectivity=2)
    (room : G.vertexConnectivity<Fintype.card V-1) (minimum : 3≤G.minDegree)
    (large : 7≤G.secondSmallestDegree) (cap : ∀ v, G.distEven v≤G.secondSmallestDegree+1) :
    ∃ A B : Finset V, ∃ p q : V, p≠q ∧ CutSides G A B {p,q} ∧
      (G.induce (A:Set V)).Connected ∧ (G.induce (B:Set V)).Connected ∧
      2≤A.card ∧ 2≤B.card ∧
      ∀ C D T, CutSides G C D T → T.card=2 → A.card≤C.card := by
  obtain ⟨A,B,p,q,pq,sides,least⟩ := exists_least_cut (G:=G) conn room
  have size : ({p,q}:Finset V).card=2 := by simp [pq]
  have border {C D : Finset V} (cut : CutSides G C D {p,q}) :
      ∀ x∈C, ∀ y, G.Adj x y → y∉C → y∈({p,q}:Finset V) := by
    intro x hx y adj hn
    rcases cut.cover y with hy|hy|hy
    · exact (hn hy).elim
    · exact (cut.no_cross x hx y hy adj).elim
    · exact hy
  exact ⟨A,B,p,q,pq,sides,
    connected_side sides size (size.trans conn.symm) minimum large cap,
    connected_side sides.swap size (size.trans conn.symm) minimum large cap,
    sector_size _ A size sides.left_nonempty (border sides) minimum,
    sector_size _ B size sides.right_nonempty (border sides.swap) minimum,least⟩

#print axioms exists_connected_least_cut
#print axioms exists_least_cut
#print axioms connected_side
end Graph189TwoCutSelect
