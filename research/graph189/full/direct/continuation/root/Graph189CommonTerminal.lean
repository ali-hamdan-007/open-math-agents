import Graph189CutFamilies
import Graph189ValidBand
import Graph189MinimumQuotas
import Graph189MinimumCutOrder

open Finset SimpleGraph Graph189FiniteDomain
namespace Graph189CommonTerminal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- The terminal calculator bounds both true high populations at any oriented minimum cut. -/
theorem cut_bounds (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (minimum : S.card = G.vertexConnectivity)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    {r : Band} (ok : valid r = true) (rs : r.s = S.card) (rk : r.k = G.secondSmallestDegree)
    (low : r.low ≤ Fintype.card V) :
    ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) ≤ r.cap ∧
    S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ∧
    (S.card+1)*G.secondSmallestDegree+S.card+1 < Fintype.card V ∧
    r.low-r.s-1 ≤ ((A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card : ℤ) +
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  have smaller (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  have prodNat := sides.high_product hc smaller cap
  change X.card * Y.card ≤ X.card*k + S.card*(k*k) at prodNat
  have prod : (X.card : ℤ)*Y.card ≤ r.k*X.card+r.s*r.k*r.k := by
    rw [rs,rk]
    exact_mod_cast (show X.card*Y.card ≤ k*X.card+S.card*k*k by
      simpa only [Nat.mul_comm X.card k,Nat.mul_assoc] using prodNat)
  have head := Graph189MinimumQuotas.high_population_lower sides
  change (Fintype.card V : ℤ)-S.card-1 ≤ (X.card : ℤ)+Y.card at head
  have size : r.low-r.s-1 ≤ (X.card : ℤ)+Y.card := by omega
  have hxy : (X.card : ℤ) ≤ Y.card := by exact_mod_cast orient
  obtain ⟨small,big,_,_,_⟩ := Graph189ValidBand.consequences ok (Int.natCast_nonneg X.card) hxy size prod
  have bigNat : S.card*k < Y.card := by rw [rs,rk] at big; exact_mod_cast big
  have numeric := ok
  simp only [valid,decide_eq_true_eq] at numeric
  obtain ⟨hs,_,_,_,_,_,_,highOrder,_,_,_,_,_⟩ := numeric
  have order : (S.card+1)*k+S.card+1 < Fintype.card V := by
    rw [rs,rk] at highOrder
    rw [rs] at hs
    exact_mod_cast (show ((S.card : ℤ)+1)*(k:ℤ)+S.card+1 < Fintype.card V by dsimp only [k]; omega)
  exact ⟨small,bigNat,order,size⟩

/-- Every valid terminal band forces three common high contacts at every
minimum separator, oriented by the number of high vertices on its sides. -/
theorem three_common (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (minimum : S.card = G.vertexConnectivity)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (orient : (A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card ≤
      (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    {r : Band} (ok : valid r = true) (rs : r.s = S.card) (rk : r.k = G.secondSmallestDegree)
    (low : r.low ≤ Fintype.card V) :
    3 ≤ (S.filter (fun i => ∀ a ∈ A, G.secondSmallestDegree ≤ G.degree a → G.Adj a i)).card := by
  classical
  let k := G.secondSmallestDegree
  let X := A.filter (fun v => k ≤ G.degree v)
  let Y := B.filter (fun v => k ≤ G.degree v)
  let C := S.filter (fun i => ∀ a ∈ A, k ≤ G.degree a → G.Adj a i)
  let D := S.filter (fun i => ∃ a ∈ X, ¬G.Adj a i)
  change 3 ≤ C.card
  have cs : C ⊆ S := filter_subset _ _
  have diff : D = S \ C := by
    ext i
    constructor
    · intro hi
      obtain ⟨si,a,ax,na⟩ := mem_filter.mp hi
      exact mem_sdiff.mpr ⟨si,fun ci => na ((mem_filter.mp ci).2 a (mem_filter.mp ax).1 (mem_filter.mp ax).2)⟩
    · intro hi
      obtain ⟨si,nc⟩ := mem_sdiff.mp hi
      have fail : ¬∀ a ∈ A, k ≤ G.degree a → G.Adj a i := fun h => nc (mem_filter.mpr ⟨si,h⟩)
      push Not at fail
      obtain ⟨a,aa,ah,miss⟩ := fail
      exact mem_filter.mpr ⟨si,a,mem_filter.mpr ⟨aa,ah⟩,miss⟩
  have smaller (T : Finset V) (lt : T.card < S.card) :=
    Graph189CutSides.connected_after_smaller_deletion (G:=G) T (lt.trans_eq minimum)
  obtain ⟨small,bigNat,order,size⟩ := cut_bounds hc sides minimum cap orient ok rs rk low
  have hs : 5 ≤ r.s := (show 5≤r.s ∧ _ by simpa only [valid,decide_eq_true_eq] using ok).1
  have cap' (v : V) : G.distEven v ≤ k+1 := by simpa [k,Nat.add_comm] using cap v
  have contacts {i : V} (hi : i ∈ S) : ∃ a ∈ A, k≤G.degree a ∧ G.Adj a i :=
    Graph189HighLabel.all_labels_in_order_range hc sides deletion smaller cap'
      (bigNat.trans_le (card_le_card (show Y ⊆ B from filter_subset _ _))) order hi
  by_contra! csmall
  rcases Graph189CutFamilies.singleton_or_two_missing hc sides smaller deletion cap bigNat order with singles | few
  · have residual (a : V) (aa : a ∈ A) (high : k ≤ G.degree a) :
        (Graph189PortLabels.support G S a \ C).card ≤ 1 := by
      have same : (Graph189PortLabels.support G S a \ C) =
          (Graph189PortLabels.support G S a).filter (fun i => ∃ y ∈ X, ¬G.Adj y i) := by
        ext i
        constructor
        · intro hi
          obtain ⟨supp,nc⟩ := mem_sdiff.mp hi
          have hd : i ∈ D := diff.symm ▸ mem_sdiff.mpr ⟨(mem_filter.mp supp).1,nc⟩
          exact mem_filter.mpr ⟨supp,(mem_filter.mp hd).2⟩
        · intro hi
          obtain ⟨supp,x,xx,nx⟩ := mem_filter.mp hi
          exact mem_sdiff.mpr ⟨supp,fun ci => nx ((mem_filter.mp ci).2 x (mem_filter.mp xx).1 (mem_filter.mp xx).2)⟩
      rw [same]
      exact singles a (mem_filter.mpr ⟨aa,high⟩)
    by_cases empty : C = ∅
    · apply Graph189MinimumQuotas.private_impossible hc sides smaller cap' (fun _ hi => contacts hi) _ ok rs rk small size
      intro a aa high
      simpa [empty] using residual a aa high
    · have cp := card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
      exact Graph189MinimumQuotas.small_common_impossible hc sides smaller cap' C cs (by omega)
        (fun i hi => contacts (mem_sdiff.mp hi).1)
        (fun a aa h i hi => (mem_filter.mp hi).2 a aa h) residual ok rs rk size
  · change D.card ≤ 2 at few
    have cd := card_sdiff_add_card_eq_card cs
    rw [← diff] at cd
    omega

#print axioms cut_bounds
#print axioms three_common
end Graph189CommonTerminal
