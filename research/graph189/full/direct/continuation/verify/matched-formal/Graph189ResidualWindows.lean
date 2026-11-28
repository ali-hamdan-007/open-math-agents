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

theorem exact_two (hc : G.Connected) {x i y : V}
    (xi : G.Adj x i) (iy : G.Adj i y) (ne : x ≠ y) (no : ¬G.Adj x y) : G.dist x y = 2 := by
  have lo := (hc x y).one_lt_dist_of_ne_of_not_adj ne no
  have hi := hc.dist_triangle (u:=x) (v:=i) (w:=y)
  rw [dist_eq_one_iff_adj.mpr xi,dist_eq_one_iff_adj.mpr iy] at hi
  omega

variable [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]

omit [Nontrivial V] [DecidableRel G.Adj] in
theorem two_layer_budget (G : SimpleGraph V) {k : ℕ} {i : V}
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


omit [Fintype V] [Nontrivial V] [DecidableRel G.Adj] in
theorem support_card_le {U C : Finset V} (h : (U \ C).card ≤ 1) : U.card ≤ C.card+1 := by
  have h1 := card_sdiff_add_card_inter U C
  have h2 : (U ∩ C).card ≤ C.card := card_le_card inter_subset_right
  omega

private theorem own_anchor_window (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) {i a : V} (hi : i ∈ S)
    (ha : a ∈ A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)) (ai : G.Adj a i)
    {c : ℕ} (limited : (Graph189PortLabels.support G S a).card ≤ c+1)
    (Z : Finset V) (sub : Z ⊆ B) (metric : ∀ v ∈ Z, G.dist i v = 2) :
    Z.card ≤ ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).filter (G.Adj i)).card+c+1 := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let QA (i : V) := X.filter (G.Adj i)
  let EA (i : V) := X.filter (fun v => G.dist i v = 2)
  have xs : X ⊆ A := filter_subset _ _
  let Nhood := insert a (A ∩ G.neighborFinset a)
  let H := Nhood.filter (fun v => k ≤ G.degree v)
  let L := Nhood.filter (fun v => ¬ k ≤ G.degree v)
  have cs : Nhood ⊆ A := by
    intro v hv
    exact (mem_insert.mp hv).elim (fun e => e ▸ xs ha) (fun h => (mem_inter.mp h).1)
  have degree_split : G.neighborFinset a ⊆ (A ∩ G.neighborFinset a) ∪ Graph189PortLabels.support G S a := by
    intro v hv
    rcases sides.cover v with hA | hB | hS
    · exact mem_union_left _ (mem_inter.mpr ⟨hA,hv⟩)
    · exact (sides.no_cross a (xs ha) v hB ((G.mem_neighborFinset _ _).mp hv)).elim
    · exact mem_union_right _ (mem_filter.mpr ⟨hS,(G.mem_neighborFinset _ _).mp hv⟩)
  have point := limited
  have adeg := (card_le_card degree_split).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at adeg
  have hhigh := (mem_filter.mp ha).2
  have csize : k ≤ Nhood.card + c := by
    unfold Nhood
    rw [card_insert_of_notMem (show a ∉ A ∩ G.neighborFinset a from by simp)]
    omega
  have low_size : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra hne
    exact (degree_pair (G:=G) u v hne).elim (mem_filter.mp hu).2 (mem_filter.mp hv).2
  have sizes := Nhood.card_filter_add_card_filter_not (fun v => k ≤ G.degree v)
  change H.card + L.card = Nhood.card at sizes
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
  have evenDis : Disjoint (EA i) Z := by
    rw [Finset.disjoint_left]
    intro v hv hz
    exact Finset.disjoint_left.mp sides.apart (xs (mem_filter.mp hv).1) (sub hz)
  have quota := two_layer_budget G (cap i) (EA i) Z evenDis
    (fun _ hv => (mem_filter.mp hv).2) metric
  change (EA i).card + Z.card ≤ k at quota
  change Z.card ≤ (QA i).card+c+1
  omega


/-- Every family of opposite exact-two windows consumes at most X+d(c+1)
slots across the residual labels. -/
theorem residual_even_windows (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (C : Finset V) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (Z : V → Finset V) (sub : ∀ i ∈ S \ C, Z i ⊆ B)
    (metric : ∀ i ∈ S \ C, ∀ y ∈ Z i, G.dist i y = 2) :
    (∑ i ∈ S \ C, (Z i).card) ≤ (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card+
      (S \ C).card*(C.card+1) := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let D := S \ C
  let QA (i : V) := X.filter (G.Adj i)
  have labels_unique (a : V) (ha : a ∈ X) {i j : V} (hi : i ∈ D) (hj : j ∈ D)
      (ai : G.Adj a i) (aj : G.Adj a j) : i = j :=
    card_le_one_iff.mp (privatePorts a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp hi).1,ai⟩,(mem_sdiff.mp hi).2⟩)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp hj).1,aj⟩,(mem_sdiff.mp hj).2⟩)
  have A_sum : ∑ i ∈ D, (QA i).card ≤ X.card := by
    have hdis : (D : Set V).PairwiseDisjoint QA := by
      intro i hi j hj hne
      change Disjoint (QA i) (QA j)
      rw [Finset.disjoint_left]
      intro a hai haj
      obtain ⟨ha,ia⟩ := mem_filter.mp hai
      exact hne (labels_unique a ha hi hj ia.symm (mem_filter.mp haj).2.symm)
    have hsub : D.biUnion QA ⊆ X := by
      intro a ha
      obtain ⟨i,_,hai⟩ := mem_biUnion.mp ha
      exact (mem_filter.mp hai).1
    rw [← card_biUnion hdis]
    exact card_le_card hsub
  have own_row (i : V) (hi : i ∈ D) : (Z i).card ≤ (QA i).card+C.card+1 := by
    obtain ⟨a,ha,hk,edge⟩ := contacts i hi
    exact own_anchor_window hc sides cap (mem_sdiff.mp hi).1 (mem_filter.mpr ⟨ha,hk⟩) edge
      (support_card_le (privatePorts a ha hk)) (Z i) (sub i hi) (metric i hi)
  calc
    ∑ i ∈ D, (Z i).card ≤ ∑ i ∈ D, ((QA i).card+(C.card+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := own_row i hi
      omega
    _ = (∑ i ∈ D, (QA i).card) + D.card*(C.card+1) := by
      rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]
    _ ≤ _ := Nat.add_le_add_right A_sum _

#print axioms residual_even_windows
end Graph189PrivateQuota
