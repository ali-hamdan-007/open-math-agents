import Graph189CutSides
import Graph189PortLabels
import Graph189R1Metric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Graph189PrivateQuota
open Finset SimpleGraph
open scoped BigOperators
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} {G : SimpleGraph V} {A B S : Finset V}

private theorem exact_two (hc : G.Connected) {x i y : V}
    (xi : G.Adj x i) (iy : G.Adj i y) (ne : x ≠ y) (no : ¬G.Adj x y) : G.dist x y = 2 := by
  have lo := (hc x y).one_lt_dist_of_ne_of_not_adj ne no
  have hi := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  rw [dist_eq_one_iff_adj.mpr xi,dist_eq_one_iff_adj.mpr iy] at hi
  omega

private theorem private_distance (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {x y i : V} (hx : x ∈ A) (hy : y ∈ B) (hmax : G.dist x y ≤ 4)
    (one : ∀ j ∈ S, G.Adj x j → j = i)
    (nonport : ∀ j ∈ S, ¬G.Adj y j) (notTwo : G.dist i y ≠ 2) : Even (G.dist x y) := by
  classical
  by_contra hodd
  have noOne : G.dist x y ≠ 1 := fun h => sides.no_cross x hx y hy (dist_eq_one_iff_adj.mp h)
  have d3 : G.dist x y = 3 := by rw [Nat.even_iff] at hodd; omega
  obtain ⟨p,hp⟩ := (hc x y).exists_walk_length_eq_dist
  obtain ⟨j,hj,hmem⟩ := sides.meets hx hy p
  have lengths := congrArg SimpleGraph.Walk.length (Walk.take_spec p hmem)
  rw [Walk.length_append] at lengths
  have left := G.dist_le (p.takeUntil j hmem)
  have right := G.dist_le (p.dropUntil j hmem)
  have tri := hc.dist_triangle (u:=x) (v:=j) (w:=y)
  have xj0 : G.dist x j ≠ 0 := by
    intro h
    exact Finset.disjoint_left.mp sides.left_cut hx ((hc.dist_eq_zero_iff.mp h).symm ▸ hj)
  have jy0 : G.dist j y ≠ 0 := by
    intro h
    exact Finset.disjoint_left.mp sides.right_cut hy ((hc.dist_eq_zero_iff.mp h) ▸ hj)
  have jy1 : G.dist j y ≠ 1 := fun h => nonport j hj (dist_eq_one_iff_adj.mp h).symm
  have xj1 : G.dist x j = 1 := by omega
  have ji := one j hj (dist_eq_one_iff_adj.mp xj1)
  apply notTwo
  rw [←ji]
  omega

variable [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
private theorem two_layer_budget (G : SimpleGraph V) {k : ℕ} {i : V}
    (cap : G.distEven i ≤ k+1) (C D : Finset V) (dis : Disjoint C D)
    (hc2 : ∀ v ∈ C, G.dist i v = 2) (hd2 : ∀ v ∈ D, G.dist i v = 2) :
    C.card + D.card ≤ k := by
  classical
  have notMem : i ∉ C ∪ D := by
    intro h
    rcases mem_union.mp h with hc | hd
    · simpa using hc2 i hc
    · simpa using hd2 i hd
  have sub : insert i (C ∪ D) ⊆ univ.filter (fun v => Even (G.dist i v)) := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · simp
    rcases mem_union.mp hv with hc | hd
    · simp [hc2 v hc]
    · simp [hd2 v hd]
  have h := (card_le_card sub).trans cap
  rw [card_insert_of_notMem notMem,card_union_of_disjoint dis] at h
  omega

/-- The private-support quota used by the terminal finite verification. `debit`
provides the pointwise cost of a vertex's unused separator labels. Only high-side
supports must be private. -/
theorem private_quota (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a).card ≤ 1)
    (debit : ∀ a ∈ A,
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).filter
        (fun v => Even (G.dist a v))).card + S.card ≤
        G.secondSmallestDegree + (Graph189PortLabels.support G S a).card) :
    let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    ((X.card : ℤ) + Y.card) * S.card ≤
      ((S.card : ℤ)*G.secondSmallestDegree - (S.card : ℤ)*((S.card : ℤ)-1) + X.card + 1)*S.card + X.card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let P := Y.filter (fun v => ∃ i ∈ S, G.Adj v i)
  let N := Y \ P
  let QA (i : V) := X.filter (G.Adj i)
  let QB (i : V) := Y.filter (G.Adj i)
  let Z (i : V) := N.filter (fun v => G.dist i v = 2)
  let EA (i : V) := X.filter (fun v => G.dist i v = 2)
  let r := k+1-S.card
  have xs : X ⊆ A := filter_subset _ _
  have ys : Y ⊆ B := filter_subset _ _
  have ps : P ⊆ Y := filter_subset _ _
  have ns : N ⊆ Y := sdiff_subset
  have Sne : S.Nonempty := by
    obtain ⟨a,ha⟩ := sides.left_nonempty
    obtain ⟨b,hb⟩ := sides.right_nonempty
    obtain ⟨p⟩ := hc a b
    obtain ⟨i,hi,_⟩ := sides.meets ha hb p
    exact ⟨i,hi⟩
  have nonport (y : V) (hy : y ∈ N) (i : V) (hi : i ∈ S) : ¬G.Adj y i := by
    intro h
    exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨ns hy,i,hi,h⟩)
  have labels_unique (a : V) (ha : a ∈ X) {i j : V} (hi : i ∈ S) (hj : j ∈ S)
      (ai : G.Adj a i) (aj : G.Adj a j) : i = j :=
    card_le_one_iff.mp (privatePorts a (xs ha) (mem_filter.mp ha).2)
      (mem_filter.mpr ⟨hi,ai⟩) (mem_filter.mpr ⟨hj,aj⟩)
  have degree_pair_bound (a : V) (ha : a ∈ X) (b : V) (hb : b ∈ Y) : G.dist a b ≤ 4 := by
    have c' (v : V) : G.distEven v ≤ 1+k := by simpa only [k,Nat.add_comm 1] using cap v
    have top := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=a) (v:=b)).trans
      (diameter_le_five hc c')
    have n5 : G.dist a b ≠ 5 := by
      intro eq
      rcases five_endpoints hc cap a b eq with h | h
      · exact (not_lt_of_ge (mem_filter.mp ha).2) h
      · exact (not_lt_of_ge (mem_filter.mp hb).2) h
    omega
  have representative (i : V) (hi : i ∈ S) : ∃ a ∈ X, G.Adj a i := by
    obtain ⟨a,ha,hk,edge⟩ := contacts i hi
    exact ⟨a,mem_filter.mpr ⟨ha,hk⟩,edge⟩
  have s_le : S.card ≤ k+1 := by
    obtain ⟨i,hi⟩ := Sne
    obtain ⟨a,ha,_⟩ := representative i hi
    have hd := debit a (xs ha)
    have hp := privatePorts a (xs ha) (mem_filter.mp ha).2
    change _ + S.card ≤ k + _ at hd
    omega
  have rEq : r + S.card = k+1 := Nat.sub_add_cancel s_le
  have qBport (i : V) (hi : i ∈ S) : QB i ⊆ P := by
    intro y hy
    obtain ⟨hY,edge⟩ := mem_filter.mp hy
    exact mem_filter.mpr ⟨hY,i,hi,edge.symm⟩
  have opposite_row (i : V) (hi : i ∈ S) : (QB i).card ≤ r ∧
      (QB i).card + N.card ≤ r + (Z i).card := by
    obtain ⟨a,ha,ai⟩ := representative i hi
    let E := Y.filter (fun v => Even (G.dist a v))
    have hquota := debit a (xs ha)
    have hprivate := privatePorts a (xs ha) (mem_filter.mp ha).2
    change E.card + S.card ≤ k + _ at hquota
    have Ecap : E.card ≤ r := by omega
    have port_even : QB i ⊆ E := by
      intro y hy
      obtain ⟨hY,edge⟩ := mem_filter.mp hy
      have ay : a ≠ y := by
        rintro rfl
        exact Finset.disjoint_left.mp sides.apart (xs ha) (ys hY)
      exact mem_filter.mpr ⟨hY,by simp [exact_two hc ai edge ay (sides.no_cross a (xs ha) y (ys hY))]⟩
    have nonport_even : N \ Z i ⊆ E := by
      intro y hy
      obtain ⟨hn,notZ⟩ := mem_sdiff.mp hy
      have hY := ns hn
      exact mem_filter.mpr ⟨hY,private_distance hc sides (xs ha) (ys hY)
        (degree_pair_bound a ha y hY) (fun j hj aj => labels_unique a ha hj hi aj ai)
        (nonport y hn) (fun d => notZ (mem_filter.mpr ⟨hn,d⟩))⟩
    have dis : Disjoint (QB i) (N \ Z i) := by
      rw [Finset.disjoint_left]
      intro y hy hn
      exact (mem_sdiff.mp (mem_sdiff.mp hn).1).2 (qBport i hi hy)
    have h := (card_le_card (union_subset port_even nonport_even)).trans Ecap
    rw [card_union_of_disjoint dis] at h
    have eq := card_sdiff_add_card_eq_card (filter_subset (fun v => G.dist i v = 2) N)
    exact ⟨(card_le_card port_even).trans Ecap,by change (N \ Z i).card + (Z i).card = N.card at eq; omega⟩
  have own_row (i : V) (hi : i ∈ S) : (Z i).card ≤ (QA i).card+1 := by
    obtain ⟨a,ha,ai⟩ := representative i hi
    let C := insert a (A ∩ G.neighborFinset a)
    let H := C.filter (fun v => k ≤ G.degree v)
    let L := C.filter (fun v => ¬ k ≤ G.degree v)
    have cs : C ⊆ A := by
      intro v hv
      exact (mem_insert.mp hv).elim (fun e => e ▸ xs ha) (fun h => (mem_inter.mp h).1)
    have degree_split : G.neighborFinset a ⊆ (A ∩ G.neighborFinset a) ∪ Graph189PortLabels.support G S a := by
      intro v hv
      rcases sides.cover v with hA | hB | hS
      · exact mem_union_left _ (mem_inter.mpr ⟨hA,hv⟩)
      · exact (sides.no_cross a (xs ha) v hB ((G.mem_neighborFinset _ _).mp hv)).elim
      · exact mem_union_right _ (mem_filter.mpr ⟨hS,(G.mem_neighborFinset _ _).mp hv⟩)
    have point := privatePorts a (xs ha) (mem_filter.mp ha).2
    have adeg := (card_le_card degree_split).trans (card_union_le _ _)
    rw [G.card_neighborFinset_eq_degree] at adeg
    have hhigh := (mem_filter.mp ha).2
    have csize : k ≤ C.card := by
      unfold C
      rw [card_insert_of_notMem (show a ∉ A ∩ G.neighborFinset a from by simp)]
      omega
    have low_size : L.card ≤ 1 := by
      apply card_le_one.mpr
      intro u hu v hv
      by_contra hne
      exact (degree_pair (G:=G) u v hne).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
    have sizes := C.card_filter_add_card_filter_not (fun v => k ≤ G.degree v)
    change H.card + L.card = C.card at sizes
    have high_near : H ⊆ QA i ∪ EA i := by
      intro v hv
      obtain ⟨hC,dv⟩ := mem_filter.mp hv
      have hX : v ∈ X := mem_filter.mpr ⟨cs hC,dv⟩
      by_cases iv : G.Adj i v
      · exact mem_union_left _ (mem_filter.mpr ⟨hX,iv⟩)
      rcases mem_insert.mp hC with rfl | hneigh
      · exact (iv ai.symm).elim
      · have ne : i ≠ v := by
          rintro rfl
          exact Finset.disjoint_left.mp sides.left_cut (xs hX) hi
        exact mem_union_right _ (mem_filter.mpr ⟨hX,exact_two hc ai.symm
          ((G.mem_neighborFinset _ _).mp (mem_inter.mp hneigh).2) ne iv⟩)
    have nearCount := (card_le_card high_near).trans (card_union_le _ _)
    have evenDis : Disjoint (EA i) (Z i) := by
      rw [Finset.disjoint_left]
      intro v hv hz
      exact Finset.disjoint_left.mp sides.apart (xs (mem_filter.mp hv).1) (ys (ns (mem_filter.mp hz).1))
    have quota := two_layer_budget G (cap i) (EA i) (Z i) evenDis
      (fun _ hv => (mem_filter.mp hv).2) (fun _ hv => (mem_filter.mp hv).2)
    change (EA i).card + (Z i).card ≤ k at quota
    omega
  have A_sum : ∑ i ∈ S, (QA i).card ≤ X.card := by
    have hdis : (S : Set V).PairwiseDisjoint QA := by
      intro i hi j hj hne
      change Disjoint (QA i) (QA j)
      rw [Finset.disjoint_left]
      intro a hai haj
      obtain ⟨ha,ia⟩ := mem_filter.mp hai
      exact hne (labels_unique a ha hi hj ia.symm (mem_filter.mp haj).2.symm)
    have hsub : S.biUnion QA ⊆ X := by
      intro a ha
      obtain ⟨i,_,hai⟩ := mem_biUnion.mp ha
      exact (mem_filter.mp hai).1
    rw [← card_biUnion hdis]
    exact card_le_card hsub
  have ports : P.card ≤ ∑ i ∈ S, (QB i).card := by
    have hsub : P ⊆ S.biUnion QB := by
      intro y hy
      obtain ⟨hY,i,hi,edge⟩ := mem_filter.mp hy
      exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hY,edge.symm⟩⟩
    exact (card_le_card hsub).trans card_biUnion_le
  have portsCap : P.card ≤ S.card*r := ports.trans (by
    calc
      ∑ i ∈ S, (QB i).card ≤ ∑ _i ∈ S, r := Finset.sum_le_sum fun i hi => (opposite_row i hi).1
      _ = _ := by rw [Finset.sum_const,Nat.nsmul_eq_mul])
  have zSum : ∑ i ∈ S, (Z i).card ≤ X.card+S.card := by
    calc
      ∑ i ∈ S, (Z i).card ≤ ∑ i ∈ S, ((QA i).card+1) := Finset.sum_le_sum fun i hi => own_row i hi
      _ = (∑ i ∈ S, (QA i).card) + S.card := by simp [Finset.sum_add_distrib]
      _ ≤ _ := Nat.add_le_add_right A_sum _
  have rows : (∑ i ∈ S, (QB i).card) + S.card*N.card ≤ S.card*r + ∑ i ∈ S, (Z i).card := by
    calc
      _ = ∑ i ∈ S, ((QB i).card+N.card) := by rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, (r+(Z i).card) := Finset.sum_le_sum fun i hi => (opposite_row i hi).2
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]
  have net : P.card + S.card*N.card ≤ S.card*r + X.card + S.card := by omega
  have splitting : N.card + P.card = Y.card := card_sdiff_add_card_eq_card ps
  have netI : (P.card : ℤ) + (S.card : ℤ)*N.card ≤ (S.card : ℤ)*r + X.card + S.card := by exact_mod_cast net
  have pcI : (P.card : ℤ) ≤ (S.card : ℤ)*r := by exact_mod_cast portsCap
  have hsplitI : (N.card : ℤ)+P.card = Y.card := by exact_mod_cast splitting
  have hsP : (1:ℤ) ≤ S.card := by exact_mod_cast card_pos.mpr Sne
  have extra := mul_le_mul_of_nonneg_right pcI (show 0 ≤ (S.card : ℤ)-1 by omega)
  have total := congrArg (fun v : ℤ => v*(S.card : ℤ)) hsplitI
  have rI : (r : ℤ)+(S.card : ℤ) = (k : ℤ)+1 := by exact_mod_cast rEq
  have re : (S.card : ℤ)*(r : ℤ) = (S.card : ℤ)*(k : ℤ) - (S.card : ℤ)*((S.card : ℤ)-1) := by
    nlinarith only [congrArg (fun q : ℤ => (S.card : ℤ)*q) rI]
  change ((X.card : ℤ)+Y.card)*S.card ≤
    ((S.card : ℤ)*k-(S.card : ℤ)*((S.card : ℤ)-1)+X.card+1)*S.card+X.card
  rw [← re]
  nlinarith only [netI,extra,total]

#print axioms private_quota
end Graph189PrivateQuota
