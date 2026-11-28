import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Graph189MixedDebit
open Finset
open scoped BigOperators

/-- Charge a common set once after deleting it from all marked covering rows. -/
theorem trim_common_rows {V I : Type*} [DecidableEq V] [DecidableEq I]
    (B D W : Finset V) (S R : Finset I) (E : I → Finset V) (k t : ℕ)
    (subset : R ⊆ S) (active : R.Nonempty) (cover : B ⊆ D ∪ S.biUnion E)
    (dquota : D.card ≤ k)
    (row : ∀ i ∈ S, i ∉ R → (E i).card ≤ k)
    (marked : ∀ i ∈ R, (E i ∪ W).card ≤ k+t) :
    B.card + (R.card-1)*W.card ≤ (S.card+1)*k + R.card*t := by
  classical
  let F (i : I) := E i \ W
  let K := S \ R
  have cov : B ⊆ ((D ∪ W) ∪ R.biUnion F) ∪ K.biUnion E := by
    intro v hv
    rcases mem_union.mp (cover hv) with hd | he
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hd))
    obtain ⟨i,hi,he⟩ := mem_biUnion.mp he
    by_cases h : i ∈ R
    · by_cases w : v ∈ W
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ w))
      · exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨i,h,mem_sdiff.mpr ⟨he,w⟩⟩))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨i,mem_sdiff.mpr ⟨hi,h⟩,he⟩)
  have un : (K.biUnion E).card ≤ K.card*k := calc
    _ ≤ ∑ i ∈ K, (E i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ K, k := sum_le_sum fun i hi => row i (mem_sdiff.mp hi).1 (mem_sdiff.mp hi).2
    _ = _ := by simp
  have com : ∑ i ∈ R, ((F i).card + W.card) ≤ ∑ _i ∈ R, (k+t) := by
    apply sum_le_sum
    intro i hi
    exact (card_sdiff_add_card (E i) W).le.trans (marked i hi)
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul] at com
  have unions := card_le_card cov
  have j1 := card_union_le D W
  have j2 := card_union_le (D ∪ W) (R.biUnion F)
  have j3 := card_union_le ((D ∪ W) ∪ R.biUnion F) (K.biUnion E)
  have raw := card_biUnion_le (s := R) (t := F)
  have cards := card_sdiff_add_card_eq_card subset
  change K.card+R.card=S.card at cards
  have ck := congrArg (fun n : ℕ => n*k) cards
  have rpos := card_pos.mpr active
  have cw := congrArg (fun n : ℕ => n*W.card) (show R.card-1+1=R.card by omega)
  nlinarith only [unions,j1,j2,j3,raw,un,com,dquota,ck,cw]

#print axioms trim_common_rows
end Graph189MixedDebit
