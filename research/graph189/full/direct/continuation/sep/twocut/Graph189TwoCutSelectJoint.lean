import Graph189GraphPopulation
import Graph189BoundaryMatching
import Graph189MinimumCutOrder
import Graph189DistanceLayers

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeLargeComponents
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Nontrivial V] in
/-- Counts the neighbors and distance-two witnesses of one anchor in
three anticomplete regions. Their sizes and the possible low vertex are
unrestricted once each region has a high contact at this anchor. -/
private theorem count_three (S : Finset V) (W : Fin 3 → Finset V) (p : V) (pS : p∈S)
    (disj : ∀ i j, i≠j → Disjoint (W i) (W j))
    (apart : ∀ i, Disjoint S (W i))
    (closed : ∀ i, ∀ u∈W i, ∀ v, G.Adj u v → v∉W i → v∈S)
    (pick : ∀ i, ∃ x∈W i, G.Adj p x ∧ G.secondSmallestDegree≤G.degree x)
    (quota : ∀ x, (univ.filter (fun y => G.dist x y=2)).card ≤ G.secondSmallestDegree) :
    G.secondSmallestDegree+6 ≤ 6*S.card := by
  classical
  let k := G.secondSmallestDegree
  let A (i : Fin 3) := (W i).filter (G.Adj p)
  let D (i : Fin 3) := (W i).filter (fun y => G.dist p y=2)
  have inner (i : Fin 3) : k+1 ≤ S.card+(A i).card+(D i).card := by
    obtain ⟨x,xw,px,high⟩ := pick i
    have sub : insert x (G.neighborFinset x) ⊆ (S∪A i)∪D i := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨xw,px⟩))
      have adj := (G.mem_neighborFinset _ _).mp h
      by_cases vw : v∈W i
      · by_cases e : G.Adj p v
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨vw,e⟩))
        have eq : p≠v := fun h => (Finset.disjoint_left.mp (apart i)) (h ▸ pS) vw
        exact mem_union_right _ (mem_filter.mpr ⟨vw,Graph189LowDegreeTwo.two_edges px adj eq e⟩)
      · exact mem_union_left _ (mem_union_left _ (closed i x xw v adj vw))
    have bound := (card_le_card sub).trans (card_union_le (S∪A i) (D i))
    have first := card_union_le S (A i)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at bound
    change G.secondSmallestDegree+1 ≤ _
    omega
  have across (i j l : Fin 3) (ij : i≠j) (il : i≠l) (jl : j≠l) :
      (A j).card+(A l).card ≤ k := by
    obtain ⟨x,xw,px,_⟩ := pick i
    have two (t : Fin 3) (it : i≠t) (y : V) (hy : y∈A t) : G.dist x y=2 := by
      obtain ⟨yw,py⟩ := mem_filter.mp hy
      have other : y∉W i := fun h => (Finset.disjoint_left.mp (disj i t it)) h yw
      have neq : x≠y := fun eq => other (eq ▸ xw)
      have no : ¬G.Adj x y := fun e => (Finset.disjoint_left.mp (apart t)) (closed i x xw y e other) yw
      exact Graph189LowDegreeTwo.two_edges px.symm py neq no
    have sub : A j∪A l ⊆ univ.filter (fun y => G.dist x y=2) := by
      intro y hy
      exact mem_filter.mpr ⟨mem_univ _,(mem_union.mp hy).elim (two j ij y) (two l il y)⟩
    have cmp := (card_le_card sub).trans (quota x)
    have dj : Disjoint (A j) (A l) := (disj j l jl).mono (filter_subset _ _) (filter_subset _ _)
    rwa [card_union_of_disjoint dj] at cmp
  have dd (i j : Fin 3) (ij : i≠j) : Disjoint (D i) (D j) :=
    (disj i j ij).mono (filter_subset _ _) (filter_subset _ _)
  have sub : (D 0∪D 1)∪D 2 ⊆ univ.filter (fun y => G.dist p y=2) := by
    intro y hy
    have yes (i : Fin 3) (h : y∈D i) := (mem_filter.mp h).2
    exact mem_filter.mpr ⟨mem_univ _,(mem_union.mp hy).elim
      (fun h => (mem_union.mp h).elim (yes 0) (yes 1)) (yes 2)⟩
  have combined := (card_le_card sub).trans (quota p)
  rw [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dd 0 2 (by decide),dd 1 2 (by decide)⟩),
    card_union_of_disjoint (dd 0 1 (by decide))] at combined
  have h₀ := inner 0
  have h₁ := inner 1
  have h₂ := inner 2
  have a₀ := across 0 1 2 (by decide) (by decide) (by decide)
  have a₁ := across 1 0 2 (by decide) (by decide) (by decide)
  have a₂ := across 2 0 1 (by decide) (by decide) (by decide)
  change (D 0).card+(D 1).card+(D 2).card ≤ k at combined
  change k+6 ≤ 6*S.card
  omega

/-- Three disjoint components large enough to meet every vertex of a
separator impose the absolute degree bound k≤6(s−1). -/
theorem three_sides (S : Finset V) (W : Fin 3 → Finset V) (two : 2≤S.card)
    (sc : S.card≤G.vertexConnectivity) (size : ∀ i, S.card ≤ (W i).card)
    (disj : ∀ i j, i≠j → Disjoint (W i) (W j))
    (apart : ∀ i, Disjoint S (W i))
    (closed : ∀ i, ∀ u∈W i, ∀ v, G.Adj u v → v∉W i → v∈S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    G.secondSmallestDegree+6 ≤ 6*S.card := by
  classical
  have match_side (i : Fin 3) : ∃ f : S ↪ W i, ∀ t : S, G.Adj t.val (f t).val := by
    obtain ⟨T,sub,big,f,edges⟩ := Graph189ExteriorGap.matching_at_component_boundary S (W i)
      (apart i) (fun x hx y hy e => closed i x hx y e hy) le_rfl (size i)
      (fun C small => Graph189CutSides.connected_after_smaller_deletion C (small.trans_le sc))
    have eq : T=S := eq_of_subset_of_card_le sub big
    subst T
    exact ⟨f,edges⟩
  choose f edge using match_side
  obtain ⟨p,hp,q,hq,ne⟩ := one_lt_card.mp (show 1<S.card by omega)
  let a : S := ⟨p,hp⟩
  let b : S := ⟨q,hq⟩
  have neq (i j : Fin 3) : (f i a).val ≠ (f j b).val := by
    intro eq
    by_cases same : i=j
    · subst j
      exact ne (congrArg (fun s : S => s.val) ((f i).injective (Subtype.ext eq)))
    · exact (Finset.disjoint_left.mp (disj i j same)) (f i a).property (eq.symm ▸ (f j b).property)
  have high : (∀ i, G.secondSmallestDegree ≤ G.degree (f i a).val) ∨
      (∀ j, G.secondSmallestDegree ≤ G.degree (f j b).val) := by
    by_cases good : ∀ i, G.secondSmallestDegree ≤ G.degree (f i a).val
    · exact Or.inl good
    push Not at good
    obtain ⟨i,low⟩ := good
    right
    intro j
    rcases degree_pair (G:=G) (f i a).val (f j b).val (neq i j) with h|h
    · omega
    · exact h
  have quota (x : V) : (univ.filter (fun y => G.dist x y=2)).card ≤ G.secondSmallestDegree := by
    let B := univ.filter (fun y => G.dist x y=2)
    have inc : insert x B ⊆ univ.filter (fun y => Even (G.dist x y)) := by
      intro y hy
      rcases mem_insert.mp hy with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have no : x∉B := by simp [B]
    have count := card_le_card inc
    rw [card_insert_of_notMem no] at count
    change B.card+1 ≤ G.distEven x at count
    exact Nat.le_of_succ_le_succ (count.trans (cap x))
  rcases high with h|h
  · exact count_three S W p hp disj apart closed
      (fun i => ⟨_,(f i a).property,edge i a,h i⟩) quota
  · exact count_three S W q hq disj apart closed
      (fun i => ⟨_,(f i b).property,edge i b,h i⟩) quota

/-- Ambient vertices of one actual component after deleting S. -/
noncomputable def vertices (S : Finset V)
    (c : (G.induce {v : V | v∉S}).ConnectedComponent) : Finset V := by
  classical
  exact univ.filter (fun v => ∃ h : v∉S, (G.induce {u : V | u∉S}).connectedComponentMk ⟨v,h⟩=c)

/-- At most two nonsingleton components survive deletion of a minimum
separator when k>6(s−1). In particular this covers all second degrees
at least 19 at connectivities two through four. -/
theorem no_three_nonsingleton (S : Finset V) (two : 2≤S.card)
    (sc : S.card≤G.vertexConnectivity) (large : 6*(S.card-1)<G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (c : Fin 3 ↪ (G.induce {v : V | v∉S}).ConnectedComponent)
    (size : ∀ i, 1 < (vertices S (c i)).card) : False := by
  classical
  let H := G.induce {v : V | v∉S}
  let W (i : Fin 3) := vertices S (c i)
  have mem (x : V) (i : Fin 3) : x∈W i ↔ ∃ h : x∉S, H.connectedComponentMk ⟨x,h⟩=c i := by
    simp [W,vertices,H]
  have apart (i) : Disjoint S (W i) := Finset.disjoint_left.mpr (fun x hx hxW =>
    ((mem x i).mp hxW).choose hx)
  have disj (i j : Fin 3) (ne : i≠j) : Disjoint (W i) (W j) := by
    apply Finset.disjoint_left.mpr
    intro x h₁ h₂
    obtain ⟨_,e₁⟩ := (mem x i).mp h₁
    obtain ⟨_,e₂⟩ := (mem x j).mp h₂
    exact ne (c.injective (e₁.symm.trans e₂))
  have closed (i : Fin 3) (x : V) (hx : x∈W i) (y : V) (edge : G.Adj x y) (no : y∉W i) : y∈S := by
    by_contra out
    obtain ⟨h,eq⟩ := (mem x i).mp hx
    have adj : H.Adj ⟨x,h⟩ ⟨y,out⟩ := edge
    exact no ((mem y i).mpr ⟨out,(ConnectedComponent.connectedComponentMk_eq_of_adj adj).symm.trans eq⟩)
  have big (i : Fin 3) : S.card≤(W i).card := by
    obtain ⟨a,ha,b,hb,ne⟩ := one_lt_card.mp (size i)
    have bounded (x : V) (hx : x∈W i) : G.degree x+1 ≤ S.card+(W i).card := by
      have sub : insert x (G.neighborFinset x) ⊆ S∪W i := by
        intro y hy
        rcases mem_insert.mp hy with rfl|adj
        · exact mem_union_right _ hx
        by_cases inside : y∈W i
        · exact mem_union_right _ inside
        · exact mem_union_left _ (closed i x hx y ((G.mem_neighborFinset _ _).mp adj) inside)
      have count := (card_le_card sub).trans (card_union_le S (W i))
      rwa [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at count
    have h₁ := bounded a ha
    have h₂ := bounded b hb
    rcases degree_pair (G:=G) a b ne with h|h <;> omega
  have bound := three_sides S W two sc big disj apart closed cap
  omega

#print axioms three_sides
#print axioms no_three_nonsingleton
end Graph189ThreeLargeComponents

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
