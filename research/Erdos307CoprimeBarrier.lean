import PrimeBudget
import Erdos307CrossCoprime
import Mathlib.Tactic.Linarith

namespace Erdos307CoprimeBarrier

open Finset

private lemma two_le_of_mem {A : Finset ℕ} (hcard : 1 < #A) (h1 : 1 ∉ A)
    (hpair : Set.Pairwise (A : Set ℕ) Nat.Coprime) :
    ∀ a ∈ A, 2 ≤ a := by
  intro a ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hne : (A.erase 0).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha]
      omega
    obtain ⟨b, hb⟩ := hne
    have hb1 : b = 1 := by
      have h := hpair ha (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb).symm
      simpa [Nat.Coprime] using h
    exact h1 (hb1 ▸ Finset.mem_of_mem_erase hb)
  have ha1 : a ≠ 1 := fun h => h1 (h ▸ ha)
  omega

theorem union_properties {P Q : Finset ℕ} (ho : 1 ∉ P ∪ Q)
    (hP : 1 < #P) (hQ : 1 < #Q) (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    (∀ a ∈ P ∪ Q, 1 < a) ∧ Set.Pairwise (↑(P ∪ Q) : Set ℕ) Nat.Coprime ∧
    2 ≤ ∑ a ∈ P ∪ Q, (1 : ℚ) / a := by
  have hp := two_le_of_mem hP (fun h => ho (mem_union_left Q h)) hpw
  have hq := two_le_of_mem hQ (fun h => ho (mem_union_right P h)) hqw
  have hc := (Erdos307Structure.swap_products P Q (fun a ha => by have := hp a ha; omega)
    (fun a ha => by have := hq a ha; omega) hpw hqw heq).2.2
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have h := hc a ha a hb
    have h1 : a = 1 := by simpa [Nat.Coprime] using h
    exact ho (h1 ▸ mem_union_left Q ha)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases mem_union.mp ha with h | h
    · exact hp a h
    · exact hq a h
  · intro a ha b hb hn
    rcases mem_union.mp ha with ap | aq <;> rcases mem_union.mp hb with bp | bq
    · exact hpw ap bp hn
    · exact hc a ap b bq
    · exact (hc b bp a aq).symm
    · exact hqw aq bq hn
  · rw [sum_union hd]
    simp only [one_div]
    let s := ∑ p ∈ P, (p : ℚ)⁻¹
    let t := ∑ p ∈ Q, (p : ℚ)⁻¹
    change 2 ≤ s+t
    change 1 = s*t at heq
    have hs : 0 ≤ s := Finset.sum_nonneg (fun _ _ => by positivity)
    have ht : 0 ≤ t := Finset.sum_nonneg (fun _ _ => by positivity)
    by_contra! h
    nlinarith [sq_nonneg (s-t), mul_pos (sub_pos.mpr h) (show 0 < 2+(s+t) by linarith)]

/-- A solution of the coprime no-one variant needs at least 59 distinct
denominators. If it uses any composite denominator, it needs at least 60. -/
theorem witness_barrier {P Q : Finset ℕ} (ho : 1 ∉ P ∪ Q)
    (hP : 1 < #P) (hQ : 1 < #Q) (hpw : Set.Pairwise (P : Set ℕ) Nat.Coprime)
    (hqw : Set.Pairwise (Q : Set ℕ) Nat.Coprime)
    (heq : 1 = (∑ p ∈ P, (p : ℚ)⁻¹) * (∑ q ∈ Q, (q : ℚ)⁻¹)) :
    59 ≤ #(P ∪ Q) ∧ ((∃ a ∈ P ∪ Q, ¬ a.Prime) → 60 ≤ #(P ∪ Q)) := by
  obtain ⟨hA, hcop, hsum⟩ := union_properties ho hP hQ hpw hqw heq
  refine ⟨Erdos307Structure.card_ge_59_of_pairwise_coprime_reciprocal_sum_ge_two hA hcop hsum, ?_⟩
  rintro ⟨a, ha, hna⟩
  by_contra! h
  exact hna (Erdos307Structure.prime_of_pairwise_coprime_reciprocal_sum_ge_two_of_card_le_59
    hA hcop hsum (by omega) a ha)

end Erdos307CoprimeBarrier

#print axioms Erdos307CoprimeBarrier.witness_barrier
