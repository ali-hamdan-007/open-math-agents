import Graph189BoundaryMatching
import Graph189MinimumCutOrder
import Graph189DistanceLayers

open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ThreeLargeComponents
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

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
    push_neg at good
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
