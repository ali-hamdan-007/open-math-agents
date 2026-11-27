import Graph189IndependentRemotes
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Graph189PathCenterThreshold

open Finset
open scoped BigOperators

/-- In a finite cover of U, the number of points hit at least twice is
at most the total support size in excess of |U|. -/
theorem repeated_boundary_budget {V J : Type*} [DecidableEq V] [Fintype J]
    (U M : Finset V) (B : J → Finset V)
    (hMU : M ⊆ U)
    (hcover : ∀ x ∈ U, 1 ≤ ∑ j, if x ∈ B j then 1 else (0 : ℕ))
    (hrepeat : ∀ x ∈ M, 2 ≤ ∑ j, if x ∈ B j then 1 else (0 : ℕ)) :
    M.card + U.card ≤ ∑ j, (B j).card := by
  classical
  let mult (x : V) := ∑ j, if x ∈ B j then 1 else (0 : ℕ)
  have hM : 2 * M.card ≤ ∑ x ∈ M, mult x := by
    simpa [mult, Nat.mul_comm] using
      (sum_le_sum (s := M) (fun x hx => hrepeat x hx))
  have hRest : (U \ M).card ≤ ∑ x ∈ U \ M, mult x := by
    simpa [mult] using
      (sum_le_sum (s := U \ M) (fun x hx => hcover x (mem_sdiff.mp hx).1))
  have hSplit : (∑ x ∈ U \ M, mult x) + (∑ x ∈ M, mult x) =
      ∑ x ∈ U, mult x :=
    sum_sdiff hMU
  have hCardSplit := card_sdiff_add_card_eq_card hMU
  have hSum : (∑ x ∈ U, mult x) ≤ ∑ j, (B j).card := by
    dsimp [mult]
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    exact card_le_card (fun _ hx => (mem_filter.mp hx).2)
  omega

/-- Every exclusive neighbor of the center falls in M, and the center
itself is among the nonexclusive remotes. -/
theorem degree_against_exclusive_budget {V : Type*} [DecidableEq V]
    {R U M N : Finset V} {x : V}
    (hUR : U ⊆ R) (hNR : N ⊆ R) (hxR : x ∈ R) (hxU : x ∉ U) (hxN : x ∉ N)
    (hShared : N ∩ U ⊆ M) :
    N.card + U.card + 1 ≤ R.card + M.card := by
  have hx : x ∉ N ∪ U := by
    simpa only [mem_union, not_or] using And.intro hxN hxU
  have hsub : insert x (N ∪ U) ⊆ R := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact hxR
    · exact union_subset hNR hUR hy
  have hcard := card_le_card hsub
  rw [card_insert_of_notMem hx] at hcard
  have hSharedCard := card_le_card hShared
  have hsplit := card_union_add_card_inter N U
  omega

/-- The improved order branch needs the stronger degree threshold only
when the old threshold would fail. -/
theorem size_branch_arithmetic {k c n delta : ℕ}
    (hk : 12 ≤ k) (hc : 2 * c + 11 ≤ 5 * k) (hn : n ≤ c)
    (hd : k - 4 ≤ delta)
    (hstrong : 3 * k - 13 ≤ c → k - 3 ≤ delta) :
    n + 2 ≤ 3 * delta := by
  by_cases h : n + 2 ≤ 3 * (k - 4)
  · omega
  · have := hstrong (by omega)
    omega

/-- The double-boundary incidence budget excludes three-port remotes in
the improved order branch when their remote degree is at least (k-4). -/
theorem three_port_arithmetic {k c u m d : ℕ}
    (hk : 12 ≤ k) (hc : 3 * k - 13 ≤ c)
    (hu : 2 * c + 1 ≤ 3 * k - 7 + u)
    (hm : m + u ≤ 2 * k - 3)
    (hd : d + u + 1 ≤ c + m)
    (hlow : k - 4 ≤ d) : False := by omega

theorem complement_overlap_arithmetic {k c n : ℕ}
    (hk : 12 ≤ k) (hc : 2 * c + 11 ≤ 5 * k) (hn : n ≤ c) :
    n - (k - 3) < 2 * (k - 4) := by omega

#print axioms repeated_boundary_budget
#print axioms degree_against_exclusive_budget
#print axioms size_branch_arithmetic
#print axioms three_port_arithmetic
#print axioms complement_overlap_arithmetic

end Graph189PathCenterThreshold
