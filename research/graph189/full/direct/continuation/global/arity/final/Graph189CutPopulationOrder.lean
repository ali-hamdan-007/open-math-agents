import Graph189CrossOrder
import Mathlib.Tactic.Linarith

namespace Graph189CutPopulationOrder

/-- Convert the cross-population bound into the total-order bound used by the
finite search, keeping the allowance for one low vertex. -/
theorem population_order {s k n x y : ℚ} (hs : 2 ≤ s) (hks : s ≤ k)
    (hsmall : k-s ≤ x) (hxy : x ≤ y) (ht : n ≤ x+y+s+1)
    (hp : x*y ≤ k*x+s*k*k) :
    (n-2*k-1)*(k-s) ≤ s*k*k := by
  have ha : 0 ≤ k-s := by linarith
  by_cases hy : k-s ≤ y-k
  · have hgap := mul_nonneg (sub_nonneg.mpr hsmall) (sub_nonneg.mpr hy)
    have htotal := mul_le_mul_of_nonneg_right ht ha
    nlinarith only [hgap, htotal, hp]
  · have hl : n-2*k-1 ≤ 2*k := by linarith
    have hmul := mul_le_mul_of_nonneg_right hl ha
    have hss := mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg k)
    have hsk := mul_nonneg (by linarith : 0 ≤ s) (by linarith : 0 ≤ k)
    nlinarith only [hmul,hss,hsk]

open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The finite upper-order inequality at a separated pair of high populations
with the genuine even-distance capacity and separator witnesses. -/
theorem cut_order (hc : G.Connected) (A B S : Finset V)
    (separate : Disjoint A B) (source : Disjoint A S) (target : Disjoint B S)
    (diam : ∀ x ∈ A, ∀ y ∈ B, G.dist x y ≤ 4)
    (cut : ∀ x ∈ A, ∀ y ∈ B, ∀ p : G.Walk x y, ∃ i ∈ S, i ∈ p.support)
    (wa : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ A ∧ ∀ v ∈ A, ¬G.Adj w v)
    (wb : ∀ i ∈ S, ∃ w, G.Adj w i ∧ w ∉ B ∧ ∀ v ∈ B, ¬G.Adj w v)
    (k : ℕ) (cap : ∀ u, G.distEven u ≤ k+1) (hs : 2 ≤ S.card) (hks : S.card ≤ k)
    (highA : ∃ a ∈ A, k ≤ G.degree a) (hxy : A.card ≤ B.card)
    (ht : Fintype.card V ≤ A.card+B.card+S.card+1) :
    ((Fintype.card V : ℚ)-2*k-1)*((k : ℚ)-S.card) ≤ (S.card : ℚ)*k*k := by
  classical
  obtain ⟨a,ha,hdeg⟩ := highA
  have hdis : Disjoint (G.neighborFinset a) B := by
    apply Finset.disjoint_left.mpr
    intro b hab hb
    have he := (G.mem_neighborFinset a b).mp hab
    obtain ⟨i,hi,hip⟩ := cut a ha b hb (.cons he .nil)
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hip
    rcases hip with rfl|rfl
    · exact Finset.disjoint_left.mp source ha hi
    · exact Finset.disjoint_left.mp target hb hi
  have hab : a ∉ B := Finset.disjoint_left.mp separate ha
  have hnot : a ∉ G.neighborFinset a ∪ B := by simp [hab]
  have hdegCount := card_le_card (subset_univ (insert a (G.neighborFinset a ∪ B)))
  rw [card_insert_of_notMem hnot,card_union_of_disjoint hdis,G.card_neighborFinset_eq_degree,
    card_univ] at hdegCount
  have hsmall : k ≤ A.card+S.card := by omega
  have hprod := Graph189CrossPort.cut_product hc A B S separate source target diam cut wa wb k cap
  apply population_order (x := (A.card : ℚ)) (y := (B.card : ℚ))
  · exact_mod_cast hs
  · exact_mod_cast hks
  · have hh : (k : ℚ) ≤ (A.card : ℚ)+S.card := by exact_mod_cast hsmall
    linarith
  · exact_mod_cast hxy
  · exact_mod_cast ht
  · have hh : (A.card : ℚ)*B.card ≤ (A.card : ℚ)*k + (S.card : ℚ)*((k : ℚ)*k) := by
      exact_mod_cast hprod
    nlinarith only [hh]

end Graph189CutPopulationOrder

#print axioms Graph189CutPopulationOrder.population_order
#print axioms Graph189CutPopulationOrder.cut_order
