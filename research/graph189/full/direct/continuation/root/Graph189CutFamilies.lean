import Graph189CoSingleton
import Graph189HighLabel

open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189CutFamilies
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {A B S : Finset V}

/-- In the high-order branch of a genuine minimum separator, the high
smaller-side supports have at most one noncommon label each, or at most
two labels of the separator fail to be common to all high small-side vertices. -/
theorem singleton_or_two_missing (hc : G.Connected) (sides : Graph189CutSides.CutSides G A B S)
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {v : V | v ∉ T}).Connected)
    (deletion : ∀ z : V, (G.induce {v : V | v ≠ z}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1+G.secondSmallestDegree)
    (big : S.card*G.secondSmallestDegree < (B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)).card)
    (order : (S.card+1)*G.secondSmallestDegree+S.card+1 < Fintype.card V) :
    let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
    let D := S.filter (fun i => ∃ x ∈ X, ¬G.Adj x i)
    (∀ x ∈ X, ((Graph189PortLabels.support G S x).filter (fun i => ∃ y ∈ X, ¬G.Adj y i)).card ≤ 1) ∨
      D.card ≤ 2 := by
  classical
  let X := A.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let Y := B.filter (fun v => G.secondSmallestDegree ≤ G.degree v)
  let D := S.filter (fun i => ∃ x ∈ X, ¬G.Adj x i)
  change _ ∨ D.card ≤ 2
  rcases Graph189CutClassification.classify_actual hc sides smaller cap big with single | co
  · exact Or.inl single
  right
  by_contra! large
  have cap' (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa [Nat.add_comm] using cap v
  have bcard : Y.card ≤ B.card := card_le_card (filter_subset _ _)
  have each (i : V) (si : i ∈ S) : ∃ x ∈ X, G.Adj x i := by
    obtain ⟨x,xa,high,xi⟩ := Graph189HighLabel.all_labels_in_order_range hc sides deletion
      smaller cap' (big.trans_le bcard) order si
    exact ⟨x,mem_filter.mpr ⟨xa,high⟩,xi⟩
  obtain ⟨z,_⟩ := sides.left_nonempty
  let f (i : V) := if h : i ∈ D then ((mem_filter.mp h).2 : ∃ x ∈ X, ¬G.Adj x i).choose else z
  have rep (i : V) (di : i ∈ D) : f i ∈ X ∧ ¬G.Adj (f i) i := by
    simpa only [f,dif_pos di] using ((mem_filter.mp di).2 : ∃ x ∈ X, ¬G.Adj x i).choose_spec
  have spec (i : V) (di : i ∈ D) : f i ∈ A ∧ ¬G.Adj (f i) i ∧ ∀ j ∈ S, j ≠ i → G.Adj (f i) j := by
    obtain ⟨high,no⟩ := rep i di
    refine ⟨(mem_filter.mp high).1,no,?_⟩
    intro j sj ji
    by_contra nope
    have si := (mem_filter.mp di).1
    exact ji (card_le_one_iff.mp (co (f i) high)
      (mem_filter.mpr ⟨sj,nope,each j sj⟩) (mem_filter.mpr ⟨si,no,each i si⟩))
  have diam (i : V) (di : i ∈ D) (y : V) (hy : y ∈ Y) : G.dist (f i) y ≤ 4 := by
    have h := (G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc) (u:=f i) (v:=y)).trans (diameter_le_five hc cap)
    have nf : G.dist (f i) y ≠ 5 := by
      intro eq
      rcases five_endpoints hc cap' (f i) y eq with h | h
      · exact (not_lt_of_ge (mem_filter.mp (rep i di).1).2) h
      · exact (not_lt_of_ge (mem_filter.mp hy).2) h
    omega
  exact (not_lt_of_ge (Graph189CoSingleton.bound hc sides (filter_subset _ _) (filter_subset _ _)
    large spec diam cap')) big

#print axioms singleton_or_two_missing
end Graph189CutFamilies
