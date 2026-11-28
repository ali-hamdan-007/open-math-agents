import Graph189ResidualWindows

namespace Graph189PrivateQuota
open Finset SimpleGraph
open scoped BigOperators
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1

variable {V : Type*} {G : SimpleGraph V} {A B S : Finset V}

private theorem private_distance (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    {C : Finset V} {x y i : V} (hx : x ∈ A) (hy : y ∈ B) (hmax : G.dist x y ≤ 4)
    (one : ∀ j ∈ S, j ∉ C → G.Adj x j → j = i)
    (nonport : ∀ j ∈ S, ¬G.Adj y j) (missCommon : ∀ j ∈ C, G.dist j y ≠ 2)
    (notTwo : G.dist i y ≠ 2) : Even (G.dist x y) := by
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
  have jy2 : G.dist j y = 2 := by omega
  have njC : j ∉ C := fun hjC => missCommon j hjC jy2
  have ji := one j hj njC (dist_eq_one_iff_adj.mp xj1)
  apply notTwo
  rw [←ji]
  omega

variable [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj]


/-- The residual singleton quota at any common label set with a nonempty remainder. -/
theorem residual_singleton_quota (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (C : Finset V) (csub : C ⊆ S) (remain : (S \ C).Nonempty)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (contacts : ∀ i ∈ S \ C, ∃ a ∈ A, G.secondSmallestDegree ≤ G.degree a ∧ G.Adj a i)
    (common : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → ∀ i ∈ C, G.Adj a i)
    (privatePorts : ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a →
      (Graph189PortLabels.support G S a \ C).card ≤ 1)
    (debit : ∀ a ∈ A,
      ((B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).filter
        (fun v => Even (G.dist a v))).card + S.card ≤
        G.secondSmallestDegree + (Graph189PortLabels.support G S a).card) :
    let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    let d : ℤ := (S \ C).card
    ((X.card : ℤ) + Y.card) * d ≤
      ((S.card : ℤ)*G.secondSmallestDegree - d*(d-1) + X.card + C.card + 1)*d + X.card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let D := S \ C
  let P := Y.filter (fun v => ∃ i ∈ S, G.Adj v i)
  let PC := P.filter (fun v => ∃ i ∈ C, G.Adj v i)
  let PD := P \ PC
  let N := Y \ P
  let GN := N.filter (fun v => ∀ i ∈ C, G.dist i v ≠ 2)
  let HN := N \ GN
  let QB (i : V) := PD.filter (G.Adj i)
  let Z (i : V) := GN.filter (fun v => G.dist i v = 2)
  let r := k+1-D.card
  have xs : X ⊆ A := filter_subset _ _
  have ys : Y ⊆ B := filter_subset _ _
  have ps : P ⊆ Y := filter_subset _ _
  have pcs : PC ⊆ P := filter_subset _ _
  have pds : PD ⊆ P := sdiff_subset
  have ns : N ⊆ Y := sdiff_subset
  have gs : GN ⊆ N := filter_subset _ _
  have dsum : D.card + C.card = S.card := card_sdiff_add_card_eq_card csub
  have nonport (y : V) (hy : y ∈ N) (i : V) (hi : i ∈ S) : ¬G.Adj y i := by
    intro h
    exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨ns hy,i,hi,h⟩)
  have labels_unique (a : V) (ha : a ∈ X) {i j : V} (hi : i ∈ D) (hj : j ∈ D)
      (ai : G.Adj a i) (aj : G.Adj a j) : i = j :=
    card_le_one_iff.mp (privatePorts a (xs ha) (mem_filter.mp ha).2)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp hi).1,ai⟩,(mem_sdiff.mp hi).2⟩)
      (mem_sdiff.mpr ⟨mem_filter.mpr ⟨(mem_sdiff.mp hj).1,aj⟩,(mem_sdiff.mp hj).2⟩)
  have support_size (a : V) (ha : a ∈ X) : (Graph189PortLabels.support G S a).card ≤ C.card+1 :=
    support_card_le (privatePorts a (xs ha) (mem_filter.mp ha).2)
  have degree_pair_bound (a : V) (ha : a ∈ X) (b : V) (hb : b ∈ Y) : G.dist a b ≤ 4 := by
    have c' (v : V) : G.distEven v ≤ 1+k := by simpa only [Nat.add_comm] using cap v
    have top := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=a) (v:=b)).trans
      (diameter_le_five hc c')
    have n5 : G.dist a b ≠ 5 := by
      intro eq
      rcases five_endpoints hc cap a b eq with h | h
      · exact (not_lt_of_ge (mem_filter.mp ha).2) h
      · exact (not_lt_of_ge (mem_filter.mp hb).2) h
    omega

  have representative (i : V) (hi : i ∈ D) : ∃ a ∈ X, G.Adj a i := by
    obtain ⟨a,ha,hk,edge⟩ := contacts i hi
    exact ⟨a,mem_filter.mpr ⟨ha,hk⟩,edge⟩
  have d_le : D.card ≤ k+1 := by
    obtain ⟨i,hi⟩ := remain
    obtain ⟨a,ha,_⟩ := representative i hi
    have hd := debit a (xs ha)
    have hp := support_size a ha
    omega
  have rEq : r + D.card = k+1 := Nat.sub_add_cancel d_le
  have opposite_row (i : V) (hi : i ∈ D) : (QB i).card ≤ r ∧
      PC.card + (QB i).card + GN.card ≤ r + (Z i).card := by
    obtain ⟨a,ha,ai⟩ := representative i hi
    let E := Y.filter (fun v => Even (G.dist a v))
    have hquota := debit a (xs ha)
    have hprivate := support_size a ha
    change E.card + S.card ≤ k + _ at hquota
    have Ecap : E.card ≤ r := by omega
    have sees (y : V) (hy : y ∈ Y) {j : V} (aj : G.Adj a j) (jy : G.Adj j y) : y ∈ E := by
      have ay : a ≠ y := by
        rintro rfl
        exact Finset.disjoint_left.mp sides.apart (xs ha) (ys hy)
      exact mem_filter.mpr ⟨hy,by simp [exact_two hc aj jy ay (sides.no_cross a (xs ha) y (ys hy))]⟩
    have common_even : PC ⊆ E := by
      intro y hy
      obtain ⟨hP,j,hj,edge⟩ := mem_filter.mp hy
      exact sees y (ps hP) (common a (xs ha) (mem_filter.mp ha).2 j hj) edge.symm
    have port_even : QB i ⊆ E := by
      intro y hy
      obtain ⟨hP,edge⟩ := mem_filter.mp hy
      exact sees y (ps (pds hP)) ai edge
    have nonport_even : GN \ Z i ⊆ E := by
      intro y hy
      obtain ⟨hg,notZ⟩ := mem_sdiff.mp hy
      obtain ⟨hn,ncommon⟩ := mem_filter.mp hg
      have hY := ns hn
      exact mem_filter.mpr ⟨hY,private_distance hc sides (xs ha) (ys hY)
        (degree_pair_bound a ha y hY) (fun j hj jn aj => labels_unique a ha (mem_sdiff.mpr ⟨hj,jn⟩) hi aj ai)
        (nonport y hn) ncommon (fun d => notZ (mem_filter.mpr ⟨hg,d⟩))⟩
    have dis1 : Disjoint PC (QB i) := by
      rw [Finset.disjoint_left]
      intro y hy hq
      exact (mem_sdiff.mp (mem_filter.mp hq).1).2 hy
    have dis2 : Disjoint (PC ∪ QB i) (GN \ Z i) := by
      rw [Finset.disjoint_left]
      intro y hy hn
      apply (mem_sdiff.mp (gs (mem_sdiff.mp hn).1)).2
      exact (mem_union.mp hy).elim (fun hc => pcs hc) (fun hq => pds (mem_filter.mp hq).1)
    have h := (card_le_card (union_subset (union_subset common_even port_even) nonport_even)).trans Ecap
    rw [card_union_of_disjoint dis2,card_union_of_disjoint dis1] at h
    have eq := card_sdiff_add_card_eq_card (filter_subset (fun v => G.dist i v = 2) GN)
    exact ⟨(card_le_card port_even).trans Ecap,by change (GN \ Z i).card + (Z i).card = GN.card at eq; omega⟩
  have ports : PD.card ≤ ∑ i ∈ D, (QB i).card := by
    have hsub : PD ⊆ D.biUnion QB := by
      intro y hy
      obtain ⟨hP,notC⟩ := mem_sdiff.mp hy
      obtain ⟨_,i,hi,edge⟩ := mem_filter.mp hP
      have ni : i ∉ C := fun hC => notC (mem_filter.mpr ⟨hP,i,hC,edge⟩)
      exact mem_biUnion.mpr ⟨i,mem_sdiff.mpr ⟨hi,ni⟩,mem_filter.mpr ⟨hy,edge.symm⟩⟩
    exact (card_le_card hsub).trans card_biUnion_le
  have portsCap : PD.card ≤ D.card*r := ports.trans (by
    calc
      ∑ i ∈ D, (QB i).card ≤ ∑ _i ∈ D, r := Finset.sum_le_sum fun i hi => (opposite_row i hi).1
      _ = _ := by rw [Finset.sum_const,Nat.nsmul_eq_mul])
  have zSum : ∑ i ∈ D, (Z i).card ≤ X.card+D.card*(C.card+1) :=
    residual_even_windows hc sides C cap contacts privatePorts Z
      (fun _ _ y hy => ys (ns (gs (mem_filter.mp hy).1)))
      (fun _ _ _ hy => (mem_filter.mp hy).2)
  have rows : (∑ i ∈ D, (QB i).card) + D.card*(PC.card+GN.card) ≤
      D.card*r + ∑ i ∈ D, (Z i).card := by
    calc
      _ = ∑ i ∈ D, ((QB i).card+(PC.card+GN.card)) := by
        rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]
      _ ≤ ∑ i ∈ D, (r+(Z i).card) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := (opposite_row i hi).2
        omega
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul]
  have nearCommon : HN.card ≤ C.card*k := by
    let T (i : V) := HN.filter (fun v => G.dist i v = 2)
    have incl : HN ⊆ C.biUnion T := by
      intro y hy
      obtain ⟨hn,ng⟩ := mem_sdiff.mp hy
      have h : ∃ i ∈ C, G.dist i y = 2 := by
        by_contra hnone
        exact ng (mem_filter.mpr ⟨hn,fun i hi he => hnone ⟨i,hi,he⟩⟩)
      obtain ⟨i,hi,edge⟩ := h
      exact mem_biUnion.mpr ⟨i,hi,mem_filter.mpr ⟨hy,edge⟩⟩
    have bound (i : V) : (T i).card ≤ k := by
      simpa using two_layer_budget G (cap i) (T i) ∅ (disjoint_empty_right _)
        (fun v hv => (mem_filter.mp hv).2) (by simp)
    calc
      HN.card ≤ (C.biUnion T).card := card_le_card incl
      _ ≤ ∑ i ∈ C, (T i).card := card_biUnion_le
      _ ≤ ∑ _i ∈ C, k := Finset.sum_le_sum fun i _ => bound i
      _ = _ := by rw [Finset.sum_const,Nat.nsmul_eq_mul]
  have net : PD.card + D.card*(PC.card+GN.card) ≤ D.card*r + X.card+D.card*(C.card+1) := by omega
  have partP : PD.card + PC.card = P.card := card_sdiff_add_card_eq_card pcs
  have partN : HN.card + GN.card = N.card := card_sdiff_add_card_eq_card gs
  have partY : N.card + P.card = Y.card := card_sdiff_add_card_eq_card ps
  have splitting : PD.card + (PC.card+GN.card) + HN.card = Y.card := by omega
  have netI : (PD.card : ℤ) + (D.card : ℤ)*((PC.card : ℤ)+GN.card) ≤
      (D.card : ℤ)*r + X.card + (D.card : ℤ)*(C.card+1) := by exact_mod_cast net
  have pcI : (PD.card : ℤ) ≤ (D.card : ℤ)*r := by exact_mod_cast portsCap
  have hnI : (HN.card : ℤ) ≤ (C.card : ℤ)*k := by exact_mod_cast nearCommon
  have hsplitI : (PD.card : ℤ)+((PC.card : ℤ)+GN.card)+HN.card = Y.card := by exact_mod_cast splitting
  have hsP : (1:ℤ) ≤ D.card := by exact_mod_cast card_pos.mpr remain
  have extra := mul_le_mul_of_nonneg_right pcI (show 0 ≤ (D.card : ℤ)-1 by omega)
  have hcquota := mul_le_mul_of_nonneg_right hnI (show 0 ≤ (D.card : ℤ) by omega)
  have total := congrArg (fun v : ℤ => v*(D.card : ℤ)) hsplitI
  have rI : (r : ℤ)+(D.card : ℤ) = (k : ℤ)+1 := by exact_mod_cast rEq
  have dsumI : (D.card : ℤ)+(C.card : ℤ) = S.card := by exact_mod_cast dsum
  have re : (D.card : ℤ)*(r : ℤ)+(C.card : ℤ)*(k : ℤ) =
      (S.card : ℤ)*(k : ℤ) - (D.card : ℤ)*((D.card : ℤ)-1) := by
    nlinarith only [congrArg (fun q : ℤ => (D.card : ℤ)*q) rI,
      congrArg (fun q : ℤ => (k : ℤ)*q) dsumI]
  change ((X.card : ℤ)+Y.card)*D.card ≤
    ((S.card : ℤ)*k-(D.card : ℤ)*((D.card : ℤ)-1)+X.card+C.card+1)*D.card+X.card
  rw [← re]
  nlinarith only [netI,extra,hcquota,total]

/-- The residual singleton bound specializes to the all-private terminal quota. -/
theorem private_from_residual (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
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
  have Sne : S.Nonempty := by
    obtain ⟨a,ha⟩ := sides.left_nonempty
    obtain ⟨b,hb⟩ := sides.right_nonempty
    obtain ⟨p⟩ := hc a b
    obtain ⟨i,hi,_⟩ := sides.meets ha hb p
    exact ⟨i,hi⟩
  have h := residual_singleton_quota hc sides ∅ (empty_subset _)
    (by simpa using Sne) cap (fun i hi => contacts i (mem_sdiff.mp hi).1)
    (by simp) (by simpa using privatePorts) debit
  simpa using h

#print axioms residual_singleton_quota
#print axioms private_from_residual
end Graph189PrivateQuota
