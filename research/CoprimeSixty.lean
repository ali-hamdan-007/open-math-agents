import Erdos307.Sixty
import Erdos307CoprimeBarrier

namespace Erdos307CoprimeBarrier

open Finset
open scoped BigOperators

/-- A witness for the unit-free coprime variant of Erdős Problem 307 has at least
sixty distinct denominators. The prime-only case uses Bonfioli's checked theorem. -/
theorem coprimeSixty
    {P Q : Finset ℕ} (ho : 1 ∉ P ∪ Q) (hP : 1 < #P) (hQ : 1 < #Q)
    (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    60 ≤ #(P ∪ Q) := by
  by_cases h : ∃ a ∈ P ∪ Q, ¬ a.Prime
  · exact (witness_barrier ho hP hQ hpw hqw heq).2 h
  · have hprime : ∀ a ∈ P ∪ Q, a.Prime := by
      intro a ha
      by_contra hna
      exact h ⟨a, ha, hna⟩
    exact Erdos307.erdos307_sixty
      (fun p hp => hprime p (mem_union_left Q hp))
      (fun q hq => hprime q (mem_union_right P hq))
      heq.symm

#print axioms coprimeSixty

end Erdos307CoprimeBarrier
