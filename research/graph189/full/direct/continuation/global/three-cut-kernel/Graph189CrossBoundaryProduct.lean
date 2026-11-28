import Graph189MinimumCut
import Graph189BoundaryDebit

open SimpleGraph Finset
namespace Graph189CrossBoundaryProduct
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem counted_pairs (hc : G.Connected) (A B S : Finset V)
    (source : Disjoint A S) (target : Disjoint B S)
    (diam : ∀ x ∈ A, ∀ y ∈ B, G.dist x y ≤ 4)
    (through : ∀ x ∈ A, ∀ y ∈ B, ∃ i ∈ S, G.dist x y = G.dist x i + G.dist i y)
    : A.card * B.card ≤ (∑ x ∈ A, (B.filter (fun y => Even (G.dist x y))).card) + ∑ i ∈ S,
      ((A.filter (fun x => G.dist x i = 1)).card * (B.filter (fun y => G.dist i y = 2)).card +
       (A.filter (fun x => G.dist x i = 2)).card * (B.filter (fun y => G.dist i y = 1)).card) := by
  classical
  let EvenRow (x : V) := B.filter (fun y => Even (G.dist x y))
  let Cross (i : V) :=
    (A.filter (fun x => G.dist x i = 1) ×ˢ B.filter (fun y => G.dist i y = 2)) ∪
    (A.filter (fun x => G.dist x i = 2) ×ˢ B.filter (fun y => G.dist i y = 1))
  have covered : A ×ˢ B ⊆ (A.biUnion (fun x => {x} ×ˢ EvenRow x)) ∪ S.biUnion Cross := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy⟩ := mem_product.mp hxy
    by_cases parity : Even (G.dist x y)
    · apply mem_union_left
      exact mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_singleton_self _,mem_filter.mpr ⟨hy,parity⟩⟩⟩
    · obtain ⟨i,hi,route⟩ := through x hx y hy
      have left : G.dist x i ≠ 0 := fun eq => Finset.disjoint_left.mp source hx ((hc.dist_eq_zero_iff.mp eq).symm ▸ hi)
      have right : G.dist i y ≠ 0 := fun eq => Finset.disjoint_left.mp target hy ((hc.dist_eq_zero_iff.mp eq) ▸ hi)
      have hd := diam x hx y hy
      rw [Nat.even_iff] at parity
      have alternatives : (G.dist x i = 1 ∧ G.dist i y = 2) ∨
          (G.dist x i = 2 ∧ G.dist i y = 1) := by omega
      apply mem_union_right
      refine mem_biUnion.mpr ⟨i,hi,?_⟩
      rcases alternatives with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
      · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,h₁⟩, mem_filter.mpr ⟨hy,h₂⟩⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,h₁⟩, mem_filter.mpr ⟨hy,h₂⟩⟩)
  rw [← card_product]
  apply le_trans (card_le_card covered)
  apply le_trans (card_union_le _ _)
  apply Nat.add_le_add
  · apply le_trans card_biUnion_le
    simp [EvenRow]
  · apply le_trans card_biUnion_le
    apply Finset.sum_le_sum
    intro i hi
    simpa only [Cross, card_product] using
      (card_union_le
        (A.filter (fun x => G.dist x i = 1) ×ˢ B.filter (fun y => G.dist i y = 2))
        (A.filter (fun x => G.dist x i = 2) ×ˢ B.filter (fun y => G.dist i y = 1)))

private theorem charged_cut [DecidableRel G.Adj] (hc : G.Connected) (A B S : Finset V)
    (separate : Disjoint A B) (source : Disjoint A S) (target : Disjoint B S)
    (diam : ∀ x ∈ A, ∀ y ∈ B, G.dist x y ≤ 4)
    (cut : ∀ x ∈ A, ∀ y ∈ B, ∀ p : G.Walk x y, ∃ i ∈ S, i ∈ p.support)
    (wa : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ A ∧ ∀ v ∈ A, ¬G.Adj w v)
    (wb : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ B ∧ ∀ v ∈ B, ¬G.Adj w v)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1)
    (debit : ∀ x∈A, (B.filter (fun y => Even (G.dist x y))).card+S.card ≤ k+(S.filter (G.Adj x)).card) :
    A.card*B.card + A.card*S.card ≤ A.card*k + S.card*(k*k) + S.card*k := by
  classical
  let E (w : V) := (univ.filter (fun v => Even (G.dist w v))).erase w
  have quota (w : V) : (E w).card ≤ k := by
    have mem : w ∈ univ.filter (fun v => Even (G.dist w v)) := by simp
    have h := cap w
    change (univ.filter (fun v => Even (G.dist w v))).card ≤ k+1 at h
    unfold E
    rw [card_erase_of_mem mem]
    omega
  have pairQuota (i : V) (T : Finset V)
      (witness : ∃ w, G.Adj w i ∧ w ∉ T ∧ ∀ v ∈ T, ¬G.Adj w v) :
      (T.filter (fun v => G.dist i v = 1)).card ≤ k := by
    obtain ⟨w,hwi,hw,hn⟩ := witness
    apply (card_le_card (t := E w) ?_).trans (quota w)
    intro v hv
    obtain ⟨hm,hiv⟩ := mem_filter.mp hv
    have bound := hc.dist_triangle (u:=w) (v:=i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr hwi, hiv] at bound
    have distinct : v ≠ w := fun e => hw (e ▸ hm)
    have nz : G.dist w v ≠ 0 := fun e => distinct (hc.dist_eq_zero_iff.mp e).symm
    have noedge : G.dist w v ≠ 1 := fun e => hn v hm (dist_eq_one_iff_adj.mp e)
    have hd : G.dist w v = 2 := by omega
    exact mem_erase.mpr ⟨distinct, mem_filter.mpr ⟨mem_univ _, by simp [hd]⟩⟩
  have through (x : V) (hx : x ∈ A) (y : V) (hy : y ∈ B) :
      ∃ i ∈ S, G.dist x y = G.dist x i + G.dist i y := by
    obtain ⟨p,hp⟩ := (hc x y).exists_walk_length_eq_dist
    obtain ⟨i,hi,hm⟩ := cut x hx y hy p
    refine ⟨i,hi,?_⟩
    have eq := congrArg SimpleGraph.Walk.length (Walk.take_spec p hm)
    rw [Walk.length_append] at eq
    have h₁ := G.dist_le (p.takeUntil i hm)
    have h₂ := G.dist_le (p.dropUntil i hm)
    have h₃ := hc.dist_triangle (u:=x) (v:=i) (w:=y)
    omega
  let R (x : V) := (B.filter (fun y => Even (G.dist x y))).card
  let labels (x : V) := S.filter (G.Adj x)
  have edges : (∑ x ∈ A, (labels x).card) = ∑ i ∈ S, (A.filter (fun x => G.Adj x i)).card := by
    simp only [labels, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have edge_budget : (∑ i ∈ S, (A.filter (fun x => G.Adj x i)).card) ≤ S.card*k := by
    calc
      _ ≤ ∑ _i ∈ S,k := Finset.sum_le_sum fun i hi => by
        simpa only [dist_comm (u:=i), dist_eq_one_iff_adj] using pairQuota i A (wa i hi)
      _ = _ := by simp
  have even_charge := Finset.sum_le_sum debit
  simp only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at even_charge
  have cover := counted_pairs hc A B S source target diam through
  have odd_charge : (∑ i ∈ S,
      ((A.filter (fun x => G.dist x i = 1)).card * (B.filter (fun y => G.dist i y = 2)).card +
      (A.filter (fun x => G.dist x i = 2)).card * (B.filter (fun y => G.dist i y = 1)).card)) ≤
      S.card*(k*k) := by
    calc _ ≤ ∑ _ ∈ S, k*k := by
            apply Finset.sum_le_sum
            intro i hi
            let U := A.filter (fun x => G.dist x i = 2)
            let W := B.filter (fun y => G.dist i y = 2)
            have dis : Disjoint U W :=
              separate.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            have both : U.card+W.card ≤ k := by
              rw [← card_union_of_disjoint dis]
              apply (card_le_card (t := E i) ?_).trans (quota i)
              intro z hz
              rcases mem_union.mp hz with a | b
              · obtain ⟨hzA,h⟩ := mem_filter.mp a
                have hd : G.dist i z = 2 := dist_comm.trans h
                have hne : z ≠ i := fun e => disjoint_left.mp source (e ▸ hzA) hi
                exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_univ _, by simp [hd]⟩⟩
              · obtain ⟨hzB,h⟩ := mem_filter.mp b
                have hne : z ≠ i := fun e => disjoint_left.mp target (e ▸ hzB) hi
                exact mem_erase.mpr ⟨hne, mem_filter.mpr ⟨mem_univ _, by simp [h]⟩⟩
            have a₁ : (A.filter (fun x => G.dist x i = 1)).card ≤ k := by
              simpa only [dist_comm (u:=i)] using pairQuota i A (wa i hi)
            have b₁ := pairQuota i B (wb i hi)
            calc _ ≤ k * W.card + U.card * k :=
                    Nat.add_le_add (Nat.mul_le_mul_right _ a₁) (Nat.mul_le_mul_left _ b₁)
                 _ = (U.card + W.card)*k := by rw [Nat.add_mul, Nat.mul_comm k W.card, Nat.add_comm]
                 _ ≤ k*k := Nat.mul_le_mul_right k both
         _ = _ := by simp
  rw [←edges] at edge_budget
  change (∑ x ∈ A,R x)+A.card*S.card ≤ A.card*k+(∑ x ∈ A, (labels x).card) at even_charge
  change A.card*B.card ≤ (∑ x ∈ A,R x)+_ at cover
  omega


open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {A B S : Finset V} [Nontrivial V] [DecidableRel G.Adj]
/-- Every unused source-side label consumes a unit of even-distance budget.
The odd cross pairs still use the separator's 1+2 rectangles. Adding the
debits before summing sharpens the usual population product at balanced cuts. -/
theorem high_product (sides : Graph189CutSides.CutSides G A B S) (hc : G.Connected)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) :
    (A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card *
      (B.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card +
        (A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card * S.card ≤
    (A.filter (fun x => G.secondSmallestDegree ≤ G.degree x)).card * G.secondSmallestDegree +
      S.card * (G.secondSmallestDegree * G.secondSmallestDegree) + S.card * G.secondSmallestDegree := by
  classical
  let H (v : V) := G.secondSmallestDegree ≤ G.degree v
  let X := A.filter H
  let Y := B.filter H
  have left : X ⊆ A := filter_subset _ _
  have right : Y ⊆ B := filter_subset _ _
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm 1] using cap v
  refine charged_cut hc X Y S (sides.apart.mono left right)
    (sides.left_cut.mono_left left) (sides.right_cut.mono_left right) ?_ ?_ ?_ ?_ _ cap' ?_
  · intro x hx y hy
    have upper := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u := x) (v := y)).trans
      (diameter_le_five hc cap)
    have notfive : G.dist x y ≠ 5 := by
      intro d
      rcases five_endpoints hc cap' x y d with h | h
      · exact (not_lt_of_ge (mem_filter.mp hx).2) h
      · exact (not_lt_of_ge (mem_filter.mp hy).2) h
    omega
  · exact fun _ hx _ hy p => sides.meets (left hx) (right hy) p
  · intro i hi
    obtain ⟨b,hb,e⟩ := (sides.contacts_of_minimum smaller hi).2
    exact ⟨b,e,fun h => disjoint_left.mp sides.apart (left h) hb,
      fun x hx ex => sides.no_cross x (left hx) b hb ex.symm⟩
  · intro i hi
    obtain ⟨a,ha,e⟩ := (sides.contacts_of_minimum smaller hi).1
    exact ⟨a,e,fun h => disjoint_left.mp sides.apart ha (right h),
      fun y hy => sides.no_cross a ha y (right hy)⟩
  · exact fun x hx => Graph189BoundaryDebit.even_quota hc sides smaller cap' right (left hx)

#print axioms high_product
end Graph189CrossBoundaryProduct
