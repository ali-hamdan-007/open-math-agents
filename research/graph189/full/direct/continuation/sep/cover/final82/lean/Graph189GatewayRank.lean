import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset
open scoped BigOperators
namespace Graph189GatewayRank

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- At threshold t, each weak column costs t missed incidences in the rows. -/
theorem bad_column_product (W Z : Finset V) (a t : ℕ)
    (row : ∀ w∈W, (Z.filter (fun z => ¬G.Adj w z)).card ≤ a) :
    (Z.filter (fun z => t ≤ (W.filter (fun w => ¬G.Adj w z)).card)).card * t ≤ W.card*a := by
  classical
  let B := Z.filter (fun z => t ≤ (W.filter (fun w => ¬G.Adj w z)).card)
  change B.card*t ≤ W.card*a
  calc
    B.card*t = ∑ z∈B, t := by simp
    _ ≤ ∑ z∈B, (W.filter (fun w => ¬G.Adj w z)).card := by
      exact Finset.sum_le_sum (fun z hz => (Finset.mem_filter.mp hz).2)
    _ ≤ ∑ z∈Z, (W.filter (fun w => ¬G.Adj w z)).card := by
      exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ w∈W, (Z.filter (fun z => ¬G.Adj w z)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ ≤ ∑ w∈W, a := Finset.sum_le_sum row
    _ = W.card*a := by simp

/-- At least i+1 columns each touch the claimed number of distinct rows. -/
theorem best_gateway_card (W Z : Finset V) (a i : ℕ) (hi : i<Z.card)
    (row : ∀ w∈W, (Z.filter (fun z => ¬G.Adj w z)).card ≤ a) :
    i+1 ≤ (Z.filter (fun z =>
        W.card-W.card*a/(Z.card-i) ≤ (W.filter (fun w => G.Adj w z)).card)).card := by
  classical
  let b := W.card*a/(Z.card-i)
  let B := Z.filter (fun z => b+1 ≤ (W.filter (fun w => ¬G.Adj w z)).card)
  have hsub : B ⊆ Z := Finset.filter_subset _ _
  have bound : B.card*(b+1) ≤ W.card*a := bad_column_product G W Z a (b+1) row
  have few : B.card < Z.card-i := by
    by_contra! large
    have prod : (b+1)*(Z.card-i) ≤ W.card*a := by
      simpa [Nat.mul_comm] using (Nat.mul_le_mul_right (b+1) large).trans bound
    have div := (Nat.le_div_iff_mul_le (show 0<Z.card-i by omega)).2 prod
    change b+1≤b at div
    omega
  have hc := Finset.card_sdiff_of_subset hsub
  have good : Z \ B ⊆ Z.filter (fun z =>
      W.card-b ≤ (W.filter (fun w => G.Adj w z)).card) := by
    intro z hz
    obtain ⟨hzZ,hzB⟩ := Finset.mem_sdiff.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨hzZ,?_⟩
    have miss : (W.filter (fun w => ¬G.Adj w z)).card ≤ b := by
      by_contra! many
      exact hzB (Finset.mem_filter.mpr ⟨hzZ,many⟩)
    have total := Finset.card_filter_add_card_filter_not (s := W) (fun w => G.Adj w z)
    omega
  have count := Finset.card_le_card good
  change i+1 ≤ (Z.filter (fun z => W.card-b ≤ (W.filter (fun w => G.Adj w z)).card)).card
  omega

#print axioms bad_column_product
#print axioms best_gateway_card
end Graph189GatewayRank
