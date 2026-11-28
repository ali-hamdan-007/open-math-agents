import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace Graph189ResidualDoubleCharge
open Finset
variable {I V : Type*}

open scoped Classical in
/-- Two copies of each representative row and one copy of the separator
rows pay twice for each high vertex on the far side. The residual row
sum is kept as a single quantity for the internal-neighborhood debit. -/
theorem budget (C D : Finset I) (Y : Finset V)
    (rep near : I → V → Prop) {k : ℕ}
    (pay : ∀ y ∈ Y, (∃ i ∈ D, rep i y) ∨
      2 ≤ (C.filter (fun i => near i y)).card + (D.filter (fun i => near i y)).card)
    (rcap : ∀ i ∈ D, (Y.filter (rep i)).card ≤ k)
    (ccap : ∀ i ∈ C, (Y.filter (near i)).card ≤ k) :
    2*Y.card ≤ (2*D.card+C.card)*k + ∑ i ∈ D, (Y.filter (near i)).card := by
  classical
  have swap (R : Finset I) (p : I → V → Prop) :
      (∑ y ∈ Y, (R.filter fun i => p i y).card) =
      ∑ i ∈ R, (Y.filter fun y => p i y).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
    exact Finset.sum_comm
  have point (y : V) (hy : y ∈ Y) :
      2 ≤ 2*(D.filter (fun i => rep i y)).card+
        ((C.filter (fun i => near i y)).card+(D.filter (fun i => near i y)).card) := by
    rcases pay y hy with ⟨i,hi,hit⟩ | bound
    · have pos : 0 < (D.filter (fun j => rep j y)).card :=
        card_pos.mpr ⟨i,mem_filter.mpr ⟨hi,hit⟩⟩
      omega
    · omega
  have total := Finset.sum_le_sum point
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,Finset.sum_add_distrib,← Finset.mul_sum,
    swap D rep,swap C near,swap D near] at total
  have r := Finset.sum_le_sum rcap
  have c := Finset.sum_le_sum ccap
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at r c
  nlinarith only [total,r,c]

/-- Three common labels absorb the entire remaining debit as soon as
k≥2d. Equality in the upper bound is sufficient for the strict Y>sk test. -/
theorem within_cut (c d k x y : ℕ) (core : 3 ≤ c) (degree : 2*d ≤ k)
    (smaller : x ≤ k) (bound : 2*y ≤ (2*d+c)*k+x+d*(c+1)) :
    y ≤ (c+d)*k := by
  have h₁ := Nat.mul_le_mul_left (c-1) degree
  have h₂ := Nat.mul_le_mul_left d (show c+1 ≤ 2*(c-1) by omega)
  have h₃ : c-1+1 = c := by omega
  have h₄ := congrArg (fun t : ℕ => t*k) h₃
  have h₅ := congrArg (fun t : ℕ => t*d) h₃
  nlinarith only [h₁,h₂,h₄,h₅,smaller,bound]

#print axioms budget
#print axioms within_cut
end Graph189ResidualDoubleCharge
