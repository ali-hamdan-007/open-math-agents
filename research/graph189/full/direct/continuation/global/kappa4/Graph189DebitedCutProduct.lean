import Graph189BoundaryDebit
import Graph189PositiveEvenCut
import Graph189CrossPort

open SimpleGraph Finset

namespace Graph189DebitedCutProduct
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [Nontrivial V] [DecidableRel G.Adj] in
/-- Exact counts of cross pairs from the even rows and the distance-three
rectangles. No estimate for an individual row is needed here. -/
private theorem count (hc : G.Connected) (X Y S : Finset V)
    (source : Disjoint X S) (target : Disjoint Y S)
    (diam : ∀ x∈X, ∀ y∈Y, G.dist x y≤4)
    (through : ∀ x∈X, ∀ y∈Y, ∃ i∈S, G.dist x y=G.dist x i+G.dist i y) :
    X.card*Y.card ≤ (∑ x∈X, (Y.filter fun y => Even (G.dist x y)).card) +
      ∑ i∈S, ((X.filter fun x => G.dist x i=1).card*(Y.filter fun y => G.dist i y=2).card +
        (X.filter fun x => G.dist x i=2).card*(Y.filter fun y => G.dist i y=1).card) := by
  classical
  let E (x : V) := Y.filter (fun y => Even (G.dist x y))
  let O (i : V) :=
    (X.filter (fun x => G.dist x i=1) ×ˢ Y.filter (fun y => G.dist i y=2)) ∪
    (X.filter (fun x => G.dist x i=2) ×ˢ Y.filter (fun y => G.dist i y=1))
  let L := X.biUnion (fun x => {x} ×ˢ E x)
  let R := S.biUnion O
  have covered : X ×ˢ Y ⊆ L ∪ R := by
    rintro ⟨x,y⟩ h
    obtain ⟨hx,hy⟩ := mem_product.mp h
    by_cases parity : Even (G.dist x y)
    · exact mem_union_left _ (mem_biUnion.mpr ⟨x,hx,mem_product.mpr ⟨mem_singleton_self _,
        mem_filter.mpr ⟨hy,parity⟩⟩⟩)
    · obtain ⟨i,hi,route⟩ := through x hx y hy
      have left : G.dist x i≠0 := fun eq => disjoint_left.mp source hx ((hc.dist_eq_zero_iff.mp eq).symm ▸ hi)
      have right : G.dist i y≠0 := fun eq => disjoint_left.mp target hy ((hc.dist_eq_zero_iff.mp eq) ▸ hi)
      have room := diam x hx y hy
      rw [Nat.even_iff] at parity
      have split : (G.dist x i=1 ∧ G.dist i y=2) ∨ (G.dist x i=2 ∧ G.dist i y=1) := by omega
      apply mem_union_right
      refine mem_biUnion.mpr ⟨i,hi,?_⟩
      rcases split with ⟨l,r⟩|⟨l,r⟩
      · exact mem_union_left _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,l⟩,mem_filter.mpr ⟨hy,r⟩⟩)
      · exact mem_union_right _ (mem_product.mpr ⟨mem_filter.mpr ⟨hx,l⟩,mem_filter.mpr ⟨hy,r⟩⟩)
  rw [←card_product]
  apply (card_le_card covered).trans ((card_union_le L R).trans (Nat.add_le_add ?_ ?_))
  · simpa [L] using (card_biUnion_le (s:=X) (t:=fun x => {x} ×ˢ E x))
  · apply card_biUnion_le.trans
    apply sum_le_sum
    intro i _
    simpa only [O,card_product] using
      card_union_le
        (X.filter (fun x => G.dist x i=1) ×ˢ Y.filter (fun y => G.dist i y=2))
        (X.filter (fun x => G.dist x i=2) ×ˢ Y.filter (fun y => G.dist i y=1))

/-- The minimum separator charges each high source's unused labels against
its even cross-pair allowance. The odd charge keeps its exact column data. -/
theorem with_columns (hc : G.Connected) {A B S X Y : Finset V}
    (sides : Graph189CutSides.CutSides G A B S) (lX : X⊆A) (rY : Y⊆B)
    (smaller : ∀ T : Finset V, T.card<S.card → (G.induce {v : V | v∉T}).Connected)
    (cap : ∀ v, G.distEven v≤1+G.secondSmallestDegree)
    (highX : ∀ x∈X, G.secondSmallestDegree≤G.degree x)
    (highY : ∀ y∈Y, G.secondSmallestDegree≤G.degree y) :
    X.card*Y.card+X.card*S.card ≤ X.card*G.secondSmallestDegree+
      (∑ i∈S, (X.filter fun x => G.dist x i=1).card) +
      ∑ i∈S, ((X.filter fun x => G.dist x i=1).card*(Y.filter fun y => G.dist i y=2).card +
        (X.filter fun x => G.dist x i=2).card*(Y.filter fun y => G.dist i y=1).card) := by
  classical
  let k := G.secondSmallestDegree
  let supports (x : V) := (Graph189PortLabels.support G S x).card
  let E (x : V) := (Y.filter (fun y => Even (G.dist x y))).card
  have counts := count hc X Y S (sides.left_cut.mono_left lX) (sides.right_cut.mono_left rY)
    (fun x hx y hy => Graph189PositiveEvenCut.high_distance_four hc cap (highX x hx) (highY y hy))
    (fun x hx y hy => Graph189PositiveEvenCut.separator_distance hc sides (lX hx) (rY hy))
  have even (x : V) (hx : x∈X) : E x+S.card≤k+supports x :=
    Graph189BoundaryDebit.even_quota hc sides smaller
      (fun v => by simpa only [Nat.add_comm 1] using cap v) rY (lX hx)
  have eq : (∑ x∈X, supports x) = ∑ i∈S, (X.filter fun x => G.dist x i=1).card := by
    simp only [supports,Graph189PortLabels.support,card_eq_sum_ones,sum_filter,dist_eq_one_iff_adj]
    exact Finset.sum_comm
  have sum : (∑ x∈X, E x) + X.card*S.card ≤
      X.card*k + ∑ i∈S, (X.filter fun x => G.dist x i=1).card := by
    simpa only [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,eq] using Finset.sum_le_sum even
  have add := Nat.add_le_add_right counts (X.card*S.card)
  rw [Nat.add_right_comm] at add
  exact add.trans (Nat.add_le_add_right sum _)

#print axioms with_columns
end Graph189DebitedCutProduct
