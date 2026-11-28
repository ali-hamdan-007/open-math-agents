import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Graph189PortCount
open Finset

variable {V : Type*} [DecidableEq V]

def hits (S : Finset V) (x : V) : ℕ := if x ∈ S then 1 else 0

private theorem sum_hits (U S : Finset V) (hs : S ⊆ U) :
    ∑ x ∈ U, hits S x = S.card := by
  exact (Finset.card_eq_sum_ite hs).symm

/-- A vertex with exactly one incident port must touch one of the three
external boundaries. Counting incidences bounds the total remote population. -/
theorem three_ports (U A B C X Y Z : Finset V) (k : ℕ)
    (cover : U = A ∪ B ∪ C)
    (sizes : A.card < k ∧ B.card < k ∧ C.card < k)
    (small : X.card ≤ 2 ∧ Y.card ≤ 2 ∧ Z.card ≤ 2)
    (charge : ∀ x ∈ U, hits A x + hits B x + hits C x = 1 → x ∈ X ∪ Y ∪ Z) :
    2 * U.card ≤ 3 * k + 3 := by
  classical
  let D := U ∩ (X ∪ Y ∪ Z)
  have hA : A ⊆ U := by rw [cover]; intro x hx; simp [hx]
  have hB : B ⊆ U := by rw [cover]; intro x hx; simp [hx]
  have hC : C ⊆ U := by rw [cover]; intro x hx; simp [hx]
  have hD : D ⊆ U := inter_subset_left
  have hDcard : D.card ≤ X.card + Y.card + Z.card := calc
    D.card ≤ (X ∪ Y ∪ Z).card := card_le_card inter_subset_right
    _ ≤ (X ∪ Y).card + Z.card := card_union_le _ _
    _ ≤ X.card + Y.card + Z.card := Nat.add_le_add_right (card_union_le _ _) _
  have point (x : V) (hx : x ∈ U) :
      2 ≤ hits A x + hits B x + hits C x + hits D x := by
    have one : 1 ≤ hits A x + hits B x + hits C x := by
      have hh := hx
      rw [cover] at hh
      simp only [mem_union] at hh
      rcases hh with (ha | hb) | hc <;> simp [hits, *] <;> omega
    by_cases eq : hits A x + hits B x + hits C x = 1
    · have hh : x ∈ D := mem_inter.mpr ⟨hx, charge x hx eq⟩
      rw [eq]
      simp [hits, hh]
    · omega
  have total := Finset.sum_le_sum point
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul,
    sum_hits U A hA, sum_hits U B hB, sum_hits U C hC, sum_hits U D hD] at total
  omega

end Graph189PortCount

#print axioms Graph189PortCount.three_ports
